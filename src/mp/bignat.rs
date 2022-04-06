use bellperson::gadgets::boolean::AllocatedBit;
use bellperson::gadgets::boolean::Boolean;
use bellperson::gadgets::num::AllocatedNum;
use bellperson::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::PrimeField;
use rug::Integer;

use std::borrow::Borrow;
use std::cmp::{max, min, Ordering};
use std::convert::From;
use std::fmt::{self, Debug, Display, Formatter};
use std::rc::Rc;

use super::poly::Polynomial;
use util::bit::{Bit, Bitvector};
use util::convert::{f_to_nat, nat_to_f};
use util::gadget::Gadget;
use util::lazy::LazyCell;
use util::num::Num;
use OptionExt;

/// Compute the natural number represented by an array of limbs.
/// The limbs are assumed to be based the `limb_width` power of 2.
pub fn limbs_to_nat<Scalar: PrimeField, B: Borrow<Scalar>, I: DoubleEndedIterator<Item = B>>(
    limbs: I,
    limb_width: usize,
) -> Integer {
    limbs.rev().fold(Integer::from(0), |mut acc, limb| {
        acc <<= limb_width as u32;
        acc += f_to_nat(limb.borrow());
        acc
    })
}

fn int_with_n_ones(n: usize) -> Integer {
    let mut m = Integer::from(1);
    m <<= n as u32;
    m -= 1;
    m
}

/// Compute the limbs encoding a natural number.
/// The limbs are assumed to be based the `limb_width` power of 2.
pub fn nat_to_limbs<'a, Scalar: PrimeField>(
    nat: &Integer,
    limb_width: usize,
    n_limbs: usize,
) -> Result<Vec<Scalar>, SynthesisError> {
    let mask = int_with_n_ones(limb_width);
    let mut nat = nat.clone();
    if nat.significant_bits() as usize <= n_limbs * limb_width {
        Ok((0..n_limbs)
            .map(|_| {
                let r = Integer::from(&nat & &mask);
                nat >>= limb_width as u32;
                nat_to_f(&r).unwrap()
            })
            .collect())
    } else {
        eprintln!(
            "nat {} does not fit in {} limbs of width {}",
            nat, n_limbs, limb_width
        );
        Err(SynthesisError::Unsatisfiable)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct BigNatParams {
    pub min_bits: usize,
    pub max_word: Integer,
    pub limb_width: usize,
    pub n_limbs: usize,
}

impl BigNatParams {
    pub fn new(limb_width: usize, n_limbs: usize) -> Self {
        let mut max_word = Integer::from(1) << limb_width as u32;
        max_word -= 1;
        BigNatParams {
            max_word,
            n_limbs,
            limb_width,
            min_bits: 0,
        }
    }
}

/// A representation of a large natural number (a member of {0, 1, 2, ... })
#[derive(Clone)]
pub struct BigNat<Scalar: PrimeField> {
    /// The linear combinations which constrain the value of each limb of the number
    pub limbs: Vec<LinearCombination<Scalar>>,
    /// The witness values for each limb (filled at witness-time)
    pub limb_values: Option<Vec<Scalar>>,
    /// The value of the whole number (filled at witness-time)
    pub value: Option<Integer>,
    /// Parameters
    pub params: BigNatParams,
}

impl<Scalar: PrimeField> std::cmp::PartialEq for BigNat<Scalar> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.params == other.params
    }
}
impl<Scalar: PrimeField> std::cmp::Eq for BigNat<Scalar> {}

impl<Scalar: PrimeField> From<BigNat<Scalar>> for Polynomial<Scalar> {
    fn from(other: BigNat<Scalar>) -> Polynomial<Scalar> {
        Polynomial {
            coefficients: other.limbs,
            values: other.limb_values,
        }
    }
}

impl<Scalar: PrimeField> BigNat<Scalar> {
    /// Allocates a `BigNat` in the circuit with `n_limbs` limbs of width `limb_width` each.
    /// If `max_word` is missing, then it is assumed to be `(2 << limb_width) - 1`.
    /// The value is provided by a closure returning limb values.
    pub fn alloc_from_limbs<CS, F>(
        mut cs: CS,
        f: F,
        max_word: Option<Integer>,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
        F: FnOnce() -> Result<Vec<Scalar>, SynthesisError>,
    {
        let values_cell = LazyCell::new(f);
        let mut value = None;
        let mut limb_values = None;
        let limbs = (0..n_limbs)
            .map(|limb_i| {
                cs.alloc(
                    || format!("limb {}", limb_i),
                    || match *values_cell.borrow() {
                        Ok(ref vs) => {
                            if vs.len() != n_limbs {
                                eprintln!("Values do not match stated limb count");
                                return Err(SynthesisError::Unsatisfiable);
                            }
                            if value.is_none() {
                                value = Some(limbs_to_nat::<Scalar, _, _>(vs.iter(), limb_width));
                            }
                            if limb_values.is_none() {
                                limb_values = Some(vs.clone());
                            }
                            Ok(vs[limb_i])
                        }
                        // Hack b/c SynthesisError and io::Error don't implement Clone
                        Err(ref e) => Err(SynthesisError::from(std::io::Error::new(
                            std::io::ErrorKind::Other,
                            format!("{}", e),
                        ))),
                    },
                )
                .map(|v| LinearCombination::zero() + v)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            value,
            limb_values,
            limbs,
            params: BigNatParams {
                min_bits: 0,
                n_limbs,
                max_word: max_word.unwrap_or_else(|| int_with_n_ones(limb_width)),
                limb_width,
            },
        })
    }

    /// Creates a `BigNat` in the circuit from the given limbs.
    pub fn from_limbs(limbs: Vec<Num<Scalar>>, limb_width: usize) -> Self {
        let limb_values = limbs
            .iter()
            .map(|n| n.value)
            .collect::<Option<Vec<Scalar>>>();
        let value = limb_values
            .as_ref()
            .map(|values| limbs_to_nat::<Scalar, _, _>(values.iter(), limb_width));
        let max_word = int_with_n_ones(limb_width);
        Self {
            params: BigNatParams {
                min_bits: 0,
                n_limbs: limbs.len(),
                max_word,
                limb_width,
            },
            value,
            limb_values,
            limbs: limbs
                .into_iter()
                .map(|i| LinearCombination::zero() + &i.num)
                .collect(),
        }
    }

    /// Allocates a `BigNat` in the circuit with `n_limbs` limbs of width `limb_width` each.
    /// The `max_word` is gauranteed to be `(2 << limb_width) - 1`.
    /// The value is provided by a closure returning a natural number.
    pub fn alloc_from_nat<CS, F>(
        mut cs: CS,
        f: F,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
        F: FnOnce() -> Result<Integer, SynthesisError>,
    {
        let all_values_cell = LazyCell::new(|| {
            f().and_then(|v| Ok((nat_to_limbs::<Scalar>(&v, limb_width, n_limbs)?, v)))
                .map_err(Rc::new)
        });
        let mut value = None;
        let mut limb_values = Vec::new();
        let limbs = (0..n_limbs)
            .map(|limb_i| {
                cs.alloc(
                    || format!("limb {}", limb_i),
                    || match *all_values_cell.borrow() {
                        Ok((ref vs, ref v)) => {
                            if value.is_none() {
                                value = Some(v.clone());
                            }
                            limb_values.push(vs[limb_i]);
                            Ok(vs[limb_i])
                        }
                        // Hack b/c SynthesisError and io::Error don't implement Clone
                        Err(ref e) => Err(SynthesisError::from(std::io::Error::new(
                            std::io::ErrorKind::Other,
                            format!("{}", e),
                        ))),
                    },
                )
                .map(|v| LinearCombination::zero() + v)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            value,
            limb_values: if limb_values.len() > 0 {
                Some(limb_values)
            } else {
                None
            },
            limbs,
            params: BigNatParams::new(limb_width, n_limbs),
        })
    }

    /// Allocates a `BigNat` in the circuit with `n_limbs` limbs of width `limb_width` each.
    /// The `max_word` is gauranteed to be `(2 << limb_width) - 1`.
    /// The value is provided by an allocated number
    pub fn from_num<CS: ConstraintSystem<Scalar>>(
        mut cs: CS,
        n: Num<Scalar>,
        limb_width: usize,
        n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
        let bignat = Self::alloc_from_nat(
            cs.namespace(|| "bignat"),
            || {
                Ok({
                    n.value
                        .as_ref()
                        .map(|n| f_to_nat(n))
                        .ok_or(SynthesisError::AssignmentMissing)?
                })
            },
            limb_width,
            n_limbs,
        )?;

        // check if bignat equals n
        // (1) decompose `bignat` into a bitvector `bv`
        let bv = bignat.decompose(cs.namespace(|| "bv"))?;
        // (2) recompose bits and check if it equals n
        n.is_equal(cs.namespace(|| "n"), &bv)?;

        Ok(bignat)
    }

    // pub fn from_num(n: Num<Scalar>, params: BigNatParams) -> Self {
    //    Self {
    //         value: n.value.as_ref().map(|n| f_to_nat(n)),
    //         limb_values: n.value.map(|v| vec![v]),
    //         limbs: vec![n.num],
    //         params,
    //     }
    // }

    pub fn as_limbs<CS: ConstraintSystem<Scalar>>(&self) -> Vec<Num<Scalar>> {
        let mut limbs = Vec::new();
        for (i, lc) in self.limbs.iter().enumerate() {
            limbs.push(Num::new(
                self.limb_values.as_ref().map(|vs| vs[i].clone()),
                lc.clone(),
            ));
        }
        limbs
    }

    pub fn inputize<CS: ConstraintSystem<Scalar>>(&self, mut cs: CS) -> Result<(), SynthesisError> {
        for (i, l) in self.limbs.iter().enumerate() {
            let mut c = cs.namespace(|| format!("limb {}", i));
            let v = c.alloc_input(|| "alloc", || Ok(self.limb_values.as_ref().grab()?[i]))?;
            c.enforce(|| "eq", |lc| lc, |lc| lc, |lc| lc + v - l);
        }
        Ok(())
    }

    /// Constrain `self` to be equal to `other`, assuming that they're both properly carried.
    pub fn equal<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        if self.limbs.len() < other.limbs.len() {
            return other.equal(cs, self);
        }
        self.enforce_limb_width_agreement(other, "equal")?;
        let n = other.limbs.len();
        for i in 0..n {
            cs.enforce(
                || format!("equal {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc + &self.limbs[i] - &other.limbs[i],
            );
        }
        for i in n..(self.limbs.len()) {
            cs.enforce(
                || format!("equal {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc + &self.limbs[i],
            );
        }
        Ok(())
    }

    /// Takes two allocated numbers (a, b) and returns
    /// allocated boolean variable with value `true`
    /// if the `a` and `b` are equal, `false` otherwise.
    pub fn equals<CS>(
        mut cs: CS,
        a: &AllocatedNum<Scalar>,
        b: &AllocatedNum<Scalar>,
    ) -> Result<Boolean, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        // Allocate and constrain `r`: result boolean bit.
        // It equals `true` if `a` equals `b`, `false` otherwise

        let r_value = match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => Some(a == b),
            _ => None,
        };

        let r = AllocatedBit::alloc(cs.namespace(|| "r"), r_value)?;

        let delta = AllocatedNum::alloc(cs.namespace(|| "delta"), || {
            let a_value = a.get_value().unwrap();
            let b_value = b.get_value().unwrap();

            let mut delta = a_value;
            delta.sub_assign(&b_value);

            Ok(delta)
        })?;

        //
        cs.enforce(
            || "delta = (a - b)",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + delta.get_variable(),
        );

        let delta_inv = AllocatedNum::alloc(cs.namespace(|| "delta_inv"), || {
            let delta = delta.get_value().unwrap();

            if delta.is_zero().unwrap_u8() == 0 {
                Ok(Scalar::one()) // we can return any number here, it doesn't matter
            } else {
                Ok(delta.invert().unwrap())
            }
        })?;

        // Allocate `t = delta * delta_inv`
        // If `delta` is non-zero (a != b), `t` will equal 1
        // If `delta` is zero (a == b), `t` cannot equal 1

        let t = AllocatedNum::alloc(cs.namespace(|| "t"), || {
            let mut tmp = delta.get_value().unwrap();
            tmp.mul_assign(&(delta_inv.get_value().unwrap()));

            Ok(tmp)
        })?;

        // Constrain allocation:
        // t = (a - b) * delta_inv
        cs.enforce(
            || "t = (a - b) * delta_inv",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + delta_inv.get_variable(),
            |lc| lc + t.get_variable(),
        );

        // Constrain:
        // (a - b) * (t - 1) == 0
        // This enforces that correct `delta_inv` was provided,
        // and thus `t` is 1 if `(a - b)` is non zero (a != b )
        cs.enforce(
            || "(a - b) * (t - 1) == 0",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + t.get_variable() - CS::one(),
            |lc| lc,
        );

        // Constrain:
        // (a - b) * r == 0
        // This enforces that `r` is zero if `(a - b)` is non-zero (a != b)
        cs.enforce(
            || "(a - b) * r == 0",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + r.get_variable(),
            |lc| lc,
        );

        // Constrain:
        // (t - 1) * (r - 1) == 0
        // This enforces that `r` is one if `t` is not one (a == b)
        cs.enforce(
            || "(t - 1) * (r - 1) == 0",
            |lc| lc + t.get_variable() - CS::one(),
            |lc| lc + r.get_variable() - CS::one(),
            |lc| lc,
        );

        Ok(Boolean::from(r))
    }

    pub fn is_equal<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        use bellperson::gadgets::num::Num;
        let mut rolling = Boolean::Constant(true);
        if self.limbs.len() != other.limbs.len() {
            eprintln!(
                "Self has {} limbs, other {} (BigNat::is_equal)",
                self.limbs.len(),
                other.limbs.len()
            );
            return Err(SynthesisError::Unsatisfiable);
        }
        self.enforce_limb_width_agreement(other, "is_equal")?;
        let n = self.limbs.len();
        for i in 0..n {
            let self_limb = AllocatedNum::alloc(cs.namespace(|| format!("self {}", i)), || {
                Ok(self.limb_values.as_ref().grab()?[i])
            })?;
            cs.enforce(
                || format!("equal self {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc - &Num::from(self_limb.clone()).lc(Scalar::one()) + &self.limbs[i],
            );
            let other_limb = AllocatedNum::alloc(cs.namespace(|| format!("other {}", i)), || {
                Ok(other.limb_values.as_ref().grab()?[i])
            })?;
            cs.enforce(
                || format!("equal other {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc - &Num::from(other_limb.clone()).lc(Scalar::one()) + &other.limbs[i],
            );

            let b = Self::equals(
                cs.namespace(|| format!("eq {}", i)),
                &self_limb,
                &other_limb,
            )?;
            rolling = Boolean::and(cs.namespace(|| format!("and {}", i)), &b, &rolling)?;
        }
        Ok(rolling)
    }

    pub fn assert_well_formed<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        // swap the option and iterator
        let limb_values_split =
            (0..self.limbs.len()).map(|i| self.limb_values.as_ref().map(|vs| vs[i]));
        for (i, (limb, limb_value)) in self.limbs.iter().zip(limb_values_split).enumerate() {
            Num::new(limb_value, limb.clone())
                .fits_in_bits(cs.namespace(|| format!("{}", i)), self.params.limb_width)?;
        }
        Ok(())
    }

    /// Break `self` up into a bit-vector.
    pub fn decompose<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
    ) -> Result<Bitvector<Scalar>, SynthesisError> {
        let limb_values_split =
            (0..self.limbs.len()).map(|i| self.limb_values.as_ref().map(|vs| vs[i]));
        let bitvectors: Vec<Bitvector<Scalar>> = self
            .limbs
            .iter()
            .zip(limb_values_split)
            .enumerate()
            .map(|(i, (limb, limb_value))| {
                Num::new(limb_value, limb.clone()).decompose(
                    cs.namespace(|| format!("subdecmop {}", i)),
                    self.params.limb_width,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut bits = Vec::new();
        let mut values = Vec::new();
        let mut allocations = Vec::new();
        for bv in bitvectors {
            bits.extend(bv.bits);
            bv.values.map(|vs| values.extend(vs));
            allocations.extend(bv.allocations);
        }
        let values = if values.len() > 0 { Some(values) } else { None };
        Ok(Bitvector {
            bits,
            values,
            allocations,
        })
    }

    pub fn recompose(bv: &Bitvector<Scalar>, limb_width: usize) -> Self {
        let nat = BigNat::from_limbs(
            bv.bits
                .iter()
                .enumerate()
                .map(|(i, bit)| {
                    let val =
                        bv.values
                            .as_ref()
                            .map(|v| if v[i] { Scalar::one() } else { Scalar::zero() });
                    Num::new(val, bit.clone())
                })
                .collect(),
            1,
        );
        nat.group_limbs(limb_width)
    }

    pub fn enforce_full_bits<CS: ConstraintSystem<Scalar>>(
        &mut self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        let value = self
            .limb_values
            .as_ref()
            .map(|vs| vs.last().unwrap().clone());
        let lc = self.limbs.last().unwrap().clone();
        Num::new(value, lc)
            .decompose(cs.namespace(|| "decomp"), self.params.limb_width)?
            .into_bits()
            .last()
            .unwrap()
            .constrain_value(cs.namespace(|| "1"), true);
        self.params.min_bits = self.params.limb_width * self.params.n_limbs;
        Ok(())
    }

    pub fn enforce_min_bits<CS: ConstraintSystem<Scalar>>(
        &mut self,
        mut cs: CS,
        min_bits: usize,
    ) -> Result<(), SynthesisError> {
        let bits = self.decompose(cs.namespace(|| "decomp"))?.into_bits();
        let upper_bits: Vec<Bit<Scalar>> = bits.into_iter().skip(min_bits - 1).collect();
        let inverse = cs.alloc(
            || "inverse",
            || {
                Ok({
                    let mut sum = Scalar::zero();
                    for b in &upper_bits {
                        if *b.value.grab()? {
                            sum.add_assign(&Scalar::one());
                        }
                    }
                    sum = sum.invert().unwrap();
                    sum
                })
            },
        )?;
        cs.enforce(
            || "inverse exists",
            |lc| lc + inverse,
            |lc| {
                let mut sum = lc;
                for b in &upper_bits {
                    sum = sum + &b.bit;
                }
                sum
            },
            |lc| lc + CS::one(),
        );
        self.params.min_bits = min_bits;
        Ok(())
    }

    pub fn enforce_limb_width_agreement(
        &self,
        other: &Self,
        location: &str,
    ) -> Result<usize, SynthesisError> {
        if self.params.limb_width == other.params.limb_width {
            return Ok(self.params.limb_width);
        } else {
            eprintln!(
                "Limb widths {}, {}, do not agree at {}",
                self.params.limb_width, other.params.limb_width, location
            );
            return Err(SynthesisError::Unsatisfiable);
        }
    }

    /// Concatenate two numbers. `self` becomes the high-order part.
    pub fn concat(&self, other: &Self) -> Result<Self, SynthesisError> {
        let limb_width = self.enforce_limb_width_agreement(other, "concat")?;
        let min_bits = if self.params.min_bits > 0 {
            self.params.min_bits + other.params.limb_width * other.params.n_limbs
        } else {
            other.params.min_bits
        };
        let mut limbs = other.limbs.clone();
        limbs.extend(self.limbs.iter().cloned());
        let mut limb_values = other.limb_values.clone();
        limb_values.as_mut().map(|x| {
            self.limb_values
                .as_ref()
                .map(|y| x.extend(y.iter().cloned()))
        });
        let value = self.value.clone().and_then(|sv| {
            other
                .value
                .as_ref()
                .map(|ov| (sv << (other.params.limb_width * other.params.n_limbs) as u32) + ov)
        });
        Ok(Self {
            params: BigNatParams {
                min_bits,
                max_word: max(&self.params.max_word, &other.params.max_word).clone(),
                n_limbs: self.params.n_limbs + other.params.n_limbs,
                limb_width,
            },
            limb_values,
            limbs,
            value,
        })
    }

    /// Produces the natural number with the low-order `n_limbs` of `self`.
    pub fn truncate_limbs(&self, n_limbs: usize) -> Self {
        let mut new = self.clone();
        if n_limbs < new.limbs.len() {
            while new.limbs.len() > n_limbs {
                new.limbs.pop();
                if let Some(limb_value) = new.limb_values.as_mut().map(|lvs| lvs.pop().unwrap()) {
                    *new.value.as_mut().unwrap() -=
                        f_to_nat(&limb_value) << (new.limbs.len() * new.params.limb_width) as u32;
                }
            }
            new.params.n_limbs = n_limbs;
            if new.params.min_bits > new.params.n_limbs * new.params.limb_width {
                new.params.min_bits = 0;
            }
        }
        new
    }

    pub fn from_poly(poly: Polynomial<Scalar>, limb_width: usize, max_word: Integer) -> Self {
        Self {
            params: BigNatParams {
                min_bits: 0,
                max_word,
                n_limbs: poly.coefficients.len(),
                limb_width,
            },
            limbs: poly.coefficients,
            value: poly
                .values
                .as_ref()
                .map(|limb_values| limbs_to_nat::<Scalar, _, _>(limb_values.iter(), limb_width)),
            limb_values: poly.values,
        }
    }

    /// Constrain `self` to be equal to `other`, after carrying both.
    pub fn equal_when_carried<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        self.enforce_limb_width_agreement(other, "equal_when_carried")?;

        // We'll propegate carries over the first `n` limbs.
        let n = min(self.limbs.len(), other.limbs.len());
        let target_base = Integer::from(1) << self.params.limb_width as u32;
        let mut accumulated_extra = Integer::from(0usize);
        let max_word = std::cmp::max(&self.params.max_word, &other.params.max_word);
        let carry_bits = (((max_word.to_f64() * 2.0).log2() - self.params.limb_width as f64).ceil()
            + 0.1) as usize;
        let mut carry_in = Num::new(Some(Scalar::zero()), LinearCombination::zero());

        for i in 0..n {
            let carry = Num::alloc(cs.namespace(|| format!("carry value {}", i)), || {
                Ok(nat_to_f(
                    &((f_to_nat(&self.limb_values.grab()?[i])
                        + f_to_nat(&carry_in.value.unwrap())
                        + max_word
                        - f_to_nat(&other.limb_values.grab()?[i]))
                        / &target_base),
                )
                .unwrap())
            })?;
            accumulated_extra += max_word;

            cs.enforce(
                || format!("carry {}", i),
                |lc| lc,
                |lc| lc,
                |lc| {
                    lc + &carry_in.num + &self.limbs[i] - &other.limbs[i]
                        + (nat_to_f(&max_word).unwrap(), CS::one())
                        - (nat_to_f(&target_base).unwrap(), &carry.num)
                        - (
                            nat_to_f(&Integer::from(&accumulated_extra % &target_base)).unwrap(),
                            CS::one(),
                        )
                },
            );

            accumulated_extra /= &target_base;

            if i < n - 1 {
                carry.fits_in_bits(cs.namespace(|| format!("carry {} decomp", i)), carry_bits)?;
            } else {
                cs.enforce(
                    || format!("carry {} is out", i),
                    |lc| lc,
                    |lc| lc,
                    |lc| lc + &carry.num - (nat_to_f(&accumulated_extra).unwrap(), CS::one()),
                );
            }
            carry_in = Num::from(carry);
        }

        for (i, zero_limb) in self.limbs.iter().enumerate().skip(n) {
            cs.enforce(
                || format!("zero self {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc + zero_limb,
            );
        }
        for (i, zero_limb) in other.limbs.iter().enumerate().skip(n) {
            cs.enforce(
                || format!("zero other {}", i),
                |lc| lc,
                |lc| lc,
                |lc| lc + zero_limb,
            );
        }
        Ok(())
    }

    /// Constrain `self` to be equal to `other`, after carrying both.
    /// Uses regrouping internally to take full advantage of the field size and reduce the amount
    /// of carrying.
    pub fn equal_when_carried_regroup<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        self.enforce_limb_width_agreement(other, "equal_when_carried_regroup")?;
        let max_word = std::cmp::max(&self.params.max_word, &other.params.max_word);
        let carry_bits = (((max_word.to_f64() * 2.0).log2() - self.params.limb_width as f64).ceil()
            + 0.1) as usize;
        let limbs_per_group = (Scalar::CAPACITY as usize - carry_bits) / self.params.limb_width;
        let self_grouped = self.group_limbs(limbs_per_group);
        let other_grouped = other.group_limbs(limbs_per_group);
        self_grouped.equal_when_carried(cs.namespace(|| "grouped"), &other_grouped)
    }

    // Constrain `self` to divide `other`.
    pub fn divides<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        self.enforce_limb_width_agreement(other, "divides")?;
        let factor = BigNat::alloc_from_nat(
            cs.namespace(|| "product"),
            || {
                let s = self.value.grab()?;
                let o = other.value.grab()?;
                if o.is_divisible(s) {
                    Ok(Integer::from(o / s))
                } else {
                    eprintln!("Not divisible");
                    Err(SynthesisError::Unsatisfiable)
                }
            },
            other.params.limb_width,
            other.params.n_limbs,
        )?;
        // Verify that factor is in bounds
        factor.assert_well_formed(cs.namespace(|| "rangecheck"))?;
        self.verify_mult(cs.namespace(|| "multcheck"), &factor, &other)
    }

    pub fn shift<CS: ConstraintSystem<Scalar>>(&self, constant: Scalar) -> BigNat<Scalar> {
        assert!(self.limbs.len() > 0);
        let mut new = self.clone();
        assert!(new.limbs.len() > 0);
        new.limbs[0] =
            std::mem::replace(&mut new.limbs[0], LinearCombination::zero()) + (constant, CS::one());
        if let Some(vs) = new.limb_values.as_mut() {
            vs[0].add_assign(&constant);
        }
        if let Some(v) = new.value.as_mut() {
            *v += f_to_nat(&constant);
        }
        new.params.max_word += f_to_nat(&constant);
        assert!(new.params.max_word <= (Integer::from(1) << Scalar::CAPACITY));
        new
    }

    pub fn scale<CS: ConstraintSystem<Scalar>>(&self, constant: Scalar) -> BigNat<Scalar> {
        let mut new = self.clone();
        for limb in &mut new.limbs {
            *limb = LinearCombination::zero() + (constant, &*limb);
        }
        if let Some(vs) = new.limb_values.as_mut() {
            for v in vs {
                v.mul_assign(&constant);
            }
        }
        if let Some(v) = new.value.as_mut() {
            *v *= f_to_nat(&constant);
        }
        new.params.max_word *= f_to_nat(&constant);
        assert!(new.params.max_word <= (Integer::from(1) << Scalar::CAPACITY));
        new
    }

    pub fn sub<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<BigNat<Scalar>, SynthesisError> {
        let diff = BigNat::alloc_from_nat(
            cs.namespace(|| "diff"),
            || {
                let mut s = self.value.grab()?.clone();
                s -= other.value.grab()?;
                Ok(s)
            },
            self.params.limb_width,
            self.params.n_limbs,
        )?;
        let sum = other.add::<CS>(&diff)?;
        self.equal_when_carried_regroup(cs.namespace(|| "eq"), &sum)?;
        Ok(diff)
    }

    pub fn mult<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<BigNat<Scalar>, SynthesisError> {
        self.enforce_limb_width_agreement(other, "mult")?;

        let mut prod = BigNat::alloc_from_nat(
            cs.namespace(|| "product"),
            || {
                let mut s = self.value.grab()?.clone();
                s *= other.value.grab()?;
                Ok(s)
            },
            other.params.limb_width,
            other.params.n_limbs + self.params.n_limbs,
        )?;
        if self.params.min_bits > 0 && other.params.min_bits > 0 {
            prod.params.min_bits = self.params.min_bits + other.params.min_bits - 1;
        }

        prod.assert_well_formed(cs.namespace(|| "rangecheck"))?;

        // Verify that factor is in bounds
        self.verify_mult(cs.namespace(|| "multcheck"), &other, &prod)?;
        Ok(prod)
    }

    pub fn add<CS: ConstraintSystem<Scalar>>(
        &self,
        other: &Self,
    ) -> Result<BigNat<Scalar>, SynthesisError> {
        self.enforce_limb_width_agreement(other, "add")?;
        let n_limbs = max(self.params.n_limbs, other.params.n_limbs);
        let max_word = Integer::from(&self.params.max_word + &other.params.max_word);
        let limbs: Vec<LinearCombination<Scalar>> = (0..n_limbs)
            .map(|i| match (self.limbs.get(i), other.limbs.get(i)) {
                (Some(a), Some(b)) => a.clone() + b,
                (Some(a), None) => a.clone(),
                (None, Some(b)) => b.clone(),
                (None, None) => unreachable!(),
            })
            .collect();
        let limb_values: Option<Vec<Scalar>> = self.limb_values.as_ref().and_then(|x| {
            other.limb_values.as_ref().map(|y| {
                (0..n_limbs)
                    .map(|i| match (x.get(i), y.get(i)) {
                        (Some(a), Some(b)) => {
                            let mut t = a.clone();
                            t.add_assign(b);
                            t
                        }
                        (Some(a), None) => a.clone(),
                        (None, Some(a)) => a.clone(),
                        (None, None) => unreachable!(),
                    })
                    .collect()
            })
        });
        let value = self
            .value
            .as_ref()
            .and_then(|x| other.value.as_ref().map(|y| Integer::from(x + y)));
        Ok(Self {
            limb_values,
            value,
            limbs,
            params: BigNatParams {
                min_bits: max(self.params.min_bits, other.params.min_bits),
                n_limbs,
                max_word,
                limb_width: self.params.limb_width,
            },
        })
    }

    pub fn min<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let select = Bit::alloc(
            cs.namespace(|| "select"),
            self.value
                .as_ref()
                .and_then(|s| other.value.as_ref().map(|o| o < s)),
        )?;
        let (lesser, greater) = Gadget::switch(cs.namespace(|| "switch"), &select, self, other)?;
        let _diff = greater.sub(cs.namespace(|| "difference"), other)?;
        Ok(lesser)
    }

    fn verify_mult<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
        prod: &Self,
    ) -> Result<(), SynthesisError> {
        self.enforce_limb_width_agreement(other, "verify_mult, other")?;
        self.enforce_limb_width_agreement(prod, "verify_mult, prod")?;
        // Verify that factor is in bounds
        let max_word = {
            let mut x = Integer::from(min(self.params.n_limbs, other.params.n_limbs));
            x *= &self.params.max_word;
            x *= &other.params.max_word;
            x
        };
        let poly_prod = Polynomial::from(self.clone()).alloc_product(
            cs.namespace(|| "poly product"),
            &Polynomial::from(other.clone()),
        )?;
        BigNat::from_poly(poly_prod, other.params.limb_width, max_word)
            .equal_when_carried_regroup(cs.namespace(|| "equal"), prod)?;
        Ok(())
    }

    pub fn assert_product_mod<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
        modulus: &Self,
        remainder: &Self,
    ) -> Result<BigNat<Scalar>, SynthesisError> {
        self.enforce_limb_width_agreement(other, "assert_product_mod, other")?;
        self.enforce_limb_width_agreement(modulus, "assert_product_mod, modulus")?;
        self.enforce_limb_width_agreement(remainder, "assert_product_mod, remainder")?;
        let limb_width = self.params.limb_width;
        let quotient_limbs = self.limbs.len() + other.limbs.len();
        let quotient = BigNat::alloc_from_nat(
            cs.namespace(|| "quotient"),
            || {
                Ok({
                    let mut x: Integer = self.value.grab()?.clone();
                    x *= *other.value().grab()?;
                    x /= *modulus.value().grab()?;
                    x
                })
            },
            self.params.limb_width,
            quotient_limbs,
        )?;
        quotient.assert_well_formed(cs.namespace(|| "quotient rangecheck"))?;
        let a_poly = Polynomial::from(self.clone());
        let b_poly = Polynomial::from(other.clone());
        let mod_poly = Polynomial::from(modulus.clone());
        let q_poly = Polynomial::from(BigNat::from(quotient.clone()));
        let r_poly = Polynomial::from(BigNat::from(remainder.clone()));

        // a * b
        let left = a_poly.alloc_product(cs.namespace(|| "left"), &b_poly)?;
        let right_product = q_poly.alloc_product(cs.namespace(|| "right_product"), &mod_poly)?;
        // q * m + r
        let right = Polynomial::from(right_product).sum(&r_poly);

        let left_max_word = {
            let mut x = Integer::from(min(self.limbs.len(), other.limbs.len()));
            x *= &self.params.max_word;
            x *= &other.params.max_word;
            x
        };
        let right_max_word = {
            let mut x = Integer::from(std::cmp::min(quotient.limbs.len(), modulus.limbs.len()));
            x *= &quotient.params.max_word;
            x *= &modulus.params.max_word;
            x += &remainder.params.max_word;
            x
        };

        let left_int = BigNat::from_poly(Polynomial::from(left), limb_width, left_max_word);
        let right_int = BigNat::from_poly(Polynomial::from(right), limb_width, right_max_word);
        left_int.equal_when_carried_regroup(cs.namespace(|| "carry"), &right_int)?;
        Ok(quotient)
    }

    /// Compute a `BigNat` contrained to be equal to `self * other % modulus`.
    pub fn mult_mod<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
        modulus: &Self,
    ) -> Result<(BigNat<Scalar>, BigNat<Scalar>), SynthesisError> {
        self.enforce_limb_width_agreement(other, "mult_mod")?;
        let limb_width = self.params.limb_width;
        let quotient_bits =
            (self.n_bits() + other.n_bits()).saturating_sub(modulus.params.min_bits);
        let quotient_limbs = quotient_bits.saturating_sub(1) / limb_width + 1;
        let quotient = BigNat::alloc_from_nat(
            cs.namespace(|| "quotient"),
            || {
                Ok({
                    let mut x = self.value.grab()?.clone();
                    x *= other.value.grab()?;
                    x /= modulus.value.grab()?;
                    x
                })
            },
            self.params.limb_width,
            quotient_limbs,
        )?;
        quotient.assert_well_formed(cs.namespace(|| "quotient rangecheck"))?;
        let remainder = BigNat::alloc_from_nat(
            cs.namespace(|| "remainder"),
            || {
                Ok({
                    let mut x = self.value.grab()?.clone();
                    x *= other.value.grab()?;
                    x %= modulus.value.grab()?;
                    x
                })
            },
            self.params.limb_width,
            modulus.limbs.len(),
        )?;
        remainder.assert_well_formed(cs.namespace(|| "remainder rangecheck"))?;
        let a_poly = Polynomial::from(self.clone());
        let b_poly = Polynomial::from(other.clone());
        let mod_poly = Polynomial::from(modulus.clone());
        let q_poly = Polynomial::from(BigNat::from(quotient.clone()));
        let r_poly = Polynomial::from(BigNat::from(remainder.clone()));

        // a * b
        let left = a_poly.alloc_product(cs.namespace(|| "left"), &b_poly)?;
        let right_product = q_poly.alloc_product(cs.namespace(|| "right_product"), &mod_poly)?;
        // q * m + r
        let right = Polynomial::from(right_product).sum(&r_poly);

        let left_max_word = {
            let mut x = Integer::from(min(self.limbs.len(), other.limbs.len()));
            x *= &self.params.max_word;
            x *= &other.params.max_word;
            x
        };
        let right_max_word = {
            let mut x = Integer::from(std::cmp::min(quotient.limbs.len(), modulus.limbs.len()));
            x *= &quotient.params.max_word;
            x *= &modulus.params.max_word;
            x += &remainder.params.max_word;
            x
        };

        let left_int = BigNat::from_poly(Polynomial::from(left), limb_width, left_max_word);
        let right_int = BigNat::from_poly(Polynomial::from(right), limb_width, right_max_word);
        left_int.equal_when_carried_regroup(cs.namespace(|| "carry"), &right_int)?;
        Ok((quotient, remainder))
    }

    /// Compute a `BigNat` contrained to be equal to `self * other % modulus`.
    pub fn red_mod<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        modulus: &Self,
    ) -> Result<BigNat<Scalar>, SynthesisError> {
        self.enforce_limb_width_agreement(modulus, "red_mod")?;
        let limb_width = self.params.limb_width;
        let quotient_bits = self.n_bits().saturating_sub(modulus.params.min_bits);
        let quotient_limbs = quotient_bits.saturating_sub(1) / limb_width + 1;
        let quotient = BigNat::alloc_from_nat(
            cs.namespace(|| "quotient"),
            || Ok(Integer::from(self.value.grab()? / modulus.value.grab()?)),
            self.params.limb_width,
            quotient_limbs,
        )?;
        quotient.assert_well_formed(cs.namespace(|| "quotient rangecheck"))?;
        let remainder = BigNat::alloc_from_nat(
            cs.namespace(|| "remainder"),
            || Ok(Integer::from(self.value.grab()? % modulus.value.grab()?)),
            self.params.limb_width,
            modulus.limbs.len(),
        )?;
        remainder.assert_well_formed(cs.namespace(|| "remainder rangecheck"))?;
        let mod_poly = Polynomial::from(modulus.clone());
        let q_poly = Polynomial::from(BigNat::from(quotient.clone()));
        let r_poly = Polynomial::from(BigNat::from(remainder.clone()));

        // q * m + r
        let right_product = q_poly.alloc_product(cs.namespace(|| "right_product"), &mod_poly)?;
        let right = Polynomial::from(right_product).sum(&r_poly);

        let right_max_word = {
            let mut x = Integer::from(std::cmp::min(quotient.limbs.len(), modulus.limbs.len()));
            x *= &quotient.params.max_word;
            x *= &modulus.params.max_word;
            x += &remainder.params.max_word;
            x
        };

        let right_int = BigNat::from_poly(Polynomial::from(right), limb_width, right_max_word);
        self.equal_when_carried_regroup(cs.namespace(|| "carry"), &right_int)?;
        Ok(remainder)
    }

    /// Combines limbs into groups.
    pub fn group_limbs(&self, limbs_per_group: usize) -> BigNat<Scalar> {
        let n_groups = (self.limbs.len() - 1) / limbs_per_group + 1;
        let limb_values = self.limb_values.as_ref().map(|vs| {
            let mut values: Vec<Scalar> = vec![Scalar::zero(); n_groups];
            let mut shift = Scalar::one();
            let limb_block = (0..self.params.limb_width).fold(Scalar::one(), |mut l, _| {
                l = l.double();
                l
            });
            for (i, v) in vs.iter().enumerate() {
                if i % limbs_per_group == 0 {
                    shift = Scalar::one();
                }
                let mut a = shift.clone();
                // a.mul_assign(&v);
                a = a * v;
                values[i / limbs_per_group].add_assign(&a);
                shift.mul_assign(&limb_block);
            }
            values
        });
        let limbs = {
            let mut limbs: Vec<LinearCombination<Scalar>> =
                vec![LinearCombination::zero(); n_groups];
            let mut shift = Scalar::one();
            let limb_block = (0..self.params.limb_width).fold(Scalar::one(), |mut l, _| {
                l = l.double();
                l
            });
            for (i, limb) in self.limbs.iter().enumerate() {
                if i % limbs_per_group == 0 {
                    shift = Scalar::one();
                }
                limbs[i / limbs_per_group] =
                    std::mem::replace(&mut limbs[i / limbs_per_group], LinearCombination::zero())
                        + (shift.clone(), limb);
                shift.mul_assign(&limb_block);
            }
            limbs
        };
        let max_word = (0..limbs_per_group).fold(Integer::from(0), |mut acc, i| {
            acc.set_bit((i * self.params.limb_width) as u32, true);
            acc
        }) * &self.params.max_word;
        BigNat {
            params: BigNatParams {
                min_bits: self.params.min_bits,
                limb_width: self.params.limb_width * limbs_per_group,
                n_limbs: limbs.len(),
                max_word,
            },
            limbs,
            limb_values,
            value: self.value.clone(),
        }
    }

    pub fn with_n_limbs<CS: ConstraintSystem<Scalar>>(&self, n_limbs: usize) -> Self {
        match n_limbs.cmp(&self.params.n_limbs) {
            Ordering::Less => panic!("Tried to downsize the number of limbs!"),
            Ordering::Equal => self.clone(),
            Ordering::Greater => {
                let mut new = self.clone();
                new.params.n_limbs = n_limbs;
                new.limb_values.as_mut().map(|vs| {
                    while vs.len() < n_limbs {
                        vs.push(Scalar::zero())
                    }
                });
                while new.limbs.len() < n_limbs {
                    new.limbs.push(LinearCombination::zero())
                }
                new
            }
        }
    }

    pub fn one<CS: ConstraintSystem<Scalar>>(limb_width: usize) -> Self {
        BigNat {
            limb_values: Some(vec![Scalar::one()]),
            value: Some(Integer::from(1)),
            limbs: { vec![LinearCombination::zero() + CS::one()] },
            params: BigNatParams {
                min_bits: 1,
                n_limbs: 1,
                limb_width: limb_width,
                max_word: Integer::from(1),
            },
        }
    }

    pub fn n_bits(&self) -> usize {
        assert!(self.params.n_limbs > 0);
        self.params.limb_width * (self.params.n_limbs - 1)
            + self.params.max_word.significant_bits() as usize
    }
}

impl<Scalar: PrimeField> Gadget for BigNat<Scalar> {
    type Scalar = Scalar;
    type Value = Integer;
    type Params = BigNatParams;
    type Access = ();
    fn alloc<CS: ConstraintSystem<Scalar>>(
        cs: CS,
        value: Option<&Self::Value>,
        _access: (),
        params: &Self::Params,
    ) -> Result<Self, SynthesisError> {
        BigNat::alloc_from_nat(
            cs,
            || Ok(value.grab()?.clone().clone()),
            params.limb_width,
            params.n_limbs,
        )
    }
    fn value(&self) -> Option<&Integer> {
        self.value.as_ref()
    }
    fn wire_values(&self) -> Option<Vec<Scalar>> {
        self.limb_values.clone()
    }
    fn params(&self) -> &BigNatParams {
        &self.params
    }
    fn wires(&self) -> Vec<LinearCombination<Scalar>> {
        self.limbs.clone()
    }
    fn access(&self) -> &() {
        &()
    }
    fn mux<CS: ConstraintSystem<Scalar>>(
        mut cs: CS,
        s: &Bit<Scalar>,
        i0: &Self,
        i1: &Self,
    ) -> Result<Self, SynthesisError> {
        let n_limbs = max(i0.params.n_limbs, i1.params.n_limbs);
        let i0 = i0.with_n_limbs::<CS>(n_limbs);
        let i1 = i1.with_n_limbs::<CS>(n_limbs);
        let i0_wires = i0.wires();
        let i1_wires = i1.wires();
        if i0_wires.len() != i1_wires.len() || i0.params.limb_width != i1.params.limb_width {
            eprintln!("Wire mis-match in BigNat mux");
            return Err(SynthesisError::Unsatisfiable);
        }
        let value: Option<&Self::Value> = s
            .value
            .and_then(|b| if b { i1.value() } else { i0.value() });
        let out: Self = Self::alloc(
            cs.namespace(|| "out"),
            value,
            (),
            &BigNatParams {
                min_bits: min(i0.params.min_bits, i1.params.min_bits),
                max_word: max(i0.params.max_word.clone(), i1.params.max_word.clone()),
                limb_width: i0.params.limb_width,
                n_limbs: i0.params.n_limbs,
            },
        )?;
        let out_wires = out.wires();
        for (i, ((i0w, i1w), out_w)) in i0_wires
            .into_iter()
            .zip(i1_wires)
            .zip(out_wires)
            .enumerate()
        {
            cs.enforce(
                || format!("{}", i),
                |lc| lc + &s.bit,
                |lc| lc + &i1w - &i0w,
                |lc| lc + &out_w - &i0w,
            );
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::TestResult;
    use util::convert::usize_to_f;
    use util::test_helpers::*;

    pub struct CarrierInputs {
        pub a: Vec<usize>,
        pub b: Vec<usize>,
    }

    pub struct CarrierParameters {
        pub max_word: usize,
        pub limb_width: usize,
        pub n_limbs: usize,
    }

    pub struct Carrier {
        inputs: Option<CarrierInputs>,
        params: CarrierParameters,
    }

    circuit_tests! {
        carry_2limbs_trivial: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,1],
                b: vec![1,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 2,
            }
        }, true),
        carry_4limbs_trivial: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,1,1,1],
                b: vec![1,1,1,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 4,
            }
        }, true),
        carry_4limbs_wrong_trivial: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,0,1,1],
                b: vec![1,1,1,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 4,
            }
        }, false),
        carry_4limbs_1carry: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,1,0,9],
                b: vec![1,1,1,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 4,
            }
        }, true),
        carry_4limbs_2carry: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,1,9,9],
                b: vec![1,2,2,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 4,
            }
        }, true),
        carry_4limbs_2carry_wrong: (Carrier {
            inputs: Some(CarrierInputs {
                a: vec![1,1,8,9],
                b: vec![1,2,2,1],
            }),
            params: CarrierParameters {
                max_word: 10,
                limb_width: 3,
                n_limbs: 4,
            }
        }, false),
    }

    impl<Scalar: PrimeField> Circuit<Scalar> for Carrier {
        fn synthesize<CS: ConstraintSystem<Scalar>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            if let Some(a) = self.inputs.as_ref().map(|i| &i.a) {
                if a.len() != self.params.n_limbs {
                    eprintln!("Unsat: inputs/n_limbs mismatch a");
                    return Err(SynthesisError::Unsatisfiable);
                }
            }
            if let Some(b) = self.inputs.as_ref().map(|i| &i.b) {
                if b.len() != self.params.n_limbs {
                    eprintln!("Unsat: inputs/n_limbs mismatch b");
                    return Err(SynthesisError::Unsatisfiable);
                }
            }
            // Reverse the inputs so that the test cases can be written with digits in normal order
            let a = BigNat::alloc_from_limbs(
                cs.namespace(|| "a"),
                || {
                    Ok(self
                        .inputs
                        .as_ref()
                        .grab()?
                        .a
                        .iter()
                        .rev()
                        .copied()
                        .map(usize_to_f)
                        .collect())
                },
                Some(Integer::from(self.params.max_word)),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            let b = BigNat::alloc_from_limbs(
                cs.namespace(|| "b"),
                || {
                    Ok(self
                        .inputs
                        .as_ref()
                        .grab()?
                        .b
                        .iter()
                        .rev()
                        .copied()
                        .map(usize_to_f)
                        .collect())
                },
                Some(Integer::from(self.params.max_word)),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            a.equal_when_carried(cs.namespace(|| "carrier"), &b)?;
            a.equal_when_carried_regroup(cs.namespace(|| "carrier_regroup"), &b)?;
            Ok(())
        }
    }

    #[derive(Debug)]
    pub struct MultModInputs {
        pub a: Integer,
        pub b: Integer,
        pub m: Integer,
        pub q: Integer,
        pub r: Integer,
    }

    pub struct MultModParameters {
        pub limb_width: usize,
        pub n_limbs_a: usize,
        pub n_limbs_b: usize,
        pub n_limbs_m: usize,
        pub full_m: bool,
    }

    pub struct MultMod {
        inputs: Option<MultModInputs>,
        params: MultModParameters,
    }

    impl<Scalar: PrimeField> Circuit<Scalar> for MultMod {
        fn synthesize<CS: ConstraintSystem<Scalar>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let a = BigNat::alloc_from_nat(
                cs.namespace(|| "a"),
                || Ok(self.inputs.grab()?.a.clone()),
                self.params.limb_width,
                self.params.n_limbs_a,
            )?;
            let b = BigNat::alloc_from_nat(
                cs.namespace(|| "b"),
                || Ok(self.inputs.grab()?.b.clone()),
                self.params.limb_width,
                self.params.n_limbs_b,
            )?;
            let mut m = BigNat::alloc_from_nat(
                cs.namespace(|| "m"),
                || Ok(self.inputs.grab()?.m.clone()),
                self.params.limb_width,
                self.params.n_limbs_m,
            )?;
            if self.params.full_m {
                m.enforce_full_bits(cs.namespace(|| "m is full"))?;
            }
            let q = BigNat::alloc_from_nat(
                cs.namespace(|| "q"),
                || Ok(self.inputs.grab()?.q.clone()),
                self.params.limb_width,
                self.params.n_limbs_a + self.params.n_limbs_b - self.params.n_limbs_m,
            )?;
            let r = BigNat::alloc_from_nat(
                cs.namespace(|| "r"),
                || Ok(self.inputs.grab()?.r.clone()),
                self.params.limb_width,
                self.params.n_limbs_m,
            )?;
            let (qa, ra) = a.mult_mod(cs.namespace(|| "prod"), &b, &m)?;
            qa.equal(cs.namespace(|| "qcheck"), &q)?;
            ra.equal(cs.namespace(|| "rcheck"), &r)?;
            Ok(())
        }
    }

    circuit_tests! {
        mult_mod_1_by_1: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(1usize),
                b: Integer::from(1usize),
                m: Integer::from(255usize),
                q: Integer::from(0usize),
                r: Integer::from(1usize),
            }),
        }, true),
        mult_mod_1_by_0: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(1usize),
                b: Integer::from(0usize),
                m: Integer::from(255usize),
                q: Integer::from(0usize),
                r: Integer::from(0usize),
            }),
        }, true),
        mult_mod_2_by_2: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(2usize),
                b: Integer::from(2usize),
                m: Integer::from(255usize),
                q: Integer::from(0usize),
                r: Integer::from(4usize),
            }),
        }, true),
        mult_mod_16_by_16: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(16usize),
                b: Integer::from(16usize),
                m: Integer::from(255usize),
                q: Integer::from(1usize),
                r: Integer::from(1usize),
            }),
        }, true),
        mult_mod_254_by_254: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(254usize),
                b: Integer::from(254usize),
                m: Integer::from(255usize),
                q: Integer::from(253usize),
                r: Integer::from(1usize),
            }),
        }, true),
        mult_mod_254_by_254_wrong: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(254usize),
                b: Integer::from(254usize),
                m: Integer::from(255usize),
                q: Integer::from(253usize),
                r: Integer::from(0usize),
            }),
        }, false),
        mult_mod_110_by_180_mod187: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 2,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(110usize),
                b: Integer::from(180usize),
                m: Integer::from(187usize),
                q: Integer::from(105usize),
                r: Integer::from(165usize),
            }),
        }, true),
        mult_mod_2w_by_6w: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 6,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(16777215usize),
                b: Integer::from(180usize),
                m: Integer::from(255usize),
                q: Integer::from(11842740usize),
                r: Integer::from(0usize),
            }),
        }, true),
        mult_mod_2w_by_6w_test_2: ( MultMod {
            params: MultModParameters {
                limb_width: 4,
                n_limbs_a: 6,
                n_limbs_b: 2,
                n_limbs_m: 2,
                full_m: true,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(16777210usize),
                b: Integer::from(180usize),
                m: Integer::from(255usize),
                q: Integer::from(11842736usize),
                r: Integer::from(120usize),
            }),
        }, true),
        mult_mod_2048x128: ( MultMod {
            params: MultModParameters {
                limb_width: 32,
                n_limbs_a: 64,
                n_limbs_b: 4,
                n_limbs_m: 4,
                full_m: false,
            },
            inputs: Some(MultModInputs {
                a: Integer::from(16777210usize),
                b: Integer::from(180usize),
                m: Integer::from(255usize),
                q: Integer::from(11842736usize),
                r: Integer::from(120usize),
            }),
        }, true),
        mult_mod_pallas: ( MultMod {
          params: MultModParameters {
            limb_width: 32,
            n_limbs_a: 8,
            n_limbs_b: 8,
            n_limbs_m: 8,
            full_m: false,
          },
          inputs: Some(MultModInputs {
            a: Integer::from_str_radix("11572336752428856981970994795408771577024165681374400871001196932361466228192", 10).unwrap(),
            b: Integer::from_str_radix("87673389408848523602668121701204553693362841135953267897017930941776218798802", 10).unwrap(),
            m: Integer::from_str_radix("40000000000000000000000000000000224698fc094cf91b992d30ed00000001", 16).unwrap(),
            q: Integer::from_str_radix("35048542371029440058224000662033175648615707461806414787901284501179083518342", 10).unwrap(),
            r: Integer::from_str_radix("26362617993085418618858432307761590013874563896298265114483698919121453084730", 10).unwrap(),
          })
        }, true),
    }

    #[derive(Debug)]
    pub struct NumberBitDecompInputs {
        pub n: Integer,
    }

    pub struct NumberBitDecompParams {
        pub n_bits: usize,
    }

    pub struct NumberBitDecomp {
        inputs: Option<NumberBitDecompInputs>,
        params: NumberBitDecompParams,
    }

    impl<Scalar: PrimeField> Circuit<Scalar> for NumberBitDecomp {
        fn synthesize<CS: ConstraintSystem<Scalar>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let n = Num::alloc(cs.namespace(|| "n"), || {
                Ok(nat_to_f(&self.inputs.grab()?.n).unwrap())
            })?;
            n.fits_in_bits(cs.namespace(|| "fits"), self.params.n_bits)?;
            n.decompose(cs.namespace(|| "explicit decomp"), self.params.n_bits)?;
            Ok(())
        }
    }

    circuit_tests! {
        decomp_1_into_1b: (
                              NumberBitDecomp {
                                  params: NumberBitDecompParams {
                                      n_bits: 1,
                                  },
                                  inputs: Some(NumberBitDecompInputs {
                                      n: Integer::from(1usize),
                                  }),
                              },
                              true
                          ),
                          decomp_1_into_2b: (
                              NumberBitDecomp {
                                  params: NumberBitDecompParams {
                                      n_bits: 2,
                                  },
                                  inputs: Some(NumberBitDecompInputs {
                                      n: Integer::from(1usize),
                                  }),
                              },
                              true
                          ),
                          decomp_5_into_2b_fails: (
                              NumberBitDecomp {
                                  params: NumberBitDecompParams {
                                      n_bits: 2,
                                  },
                                  inputs: Some(NumberBitDecompInputs {
                                      n: Integer::from(5usize),
                                  }),
                              },
                              false
                          ),
                          decomp_255_into_8b: (
                              NumberBitDecomp {
                                  params: NumberBitDecompParams {
                                      n_bits: 8,
                                  },
                                  inputs: Some(NumberBitDecompInputs {
                                      n: Integer::from(255usize),
                                  }),
                              },
                              true
                          ),
    }

    #[derive(Debug)]
    pub struct BigNatBitDecompInputs {
        pub n: Integer,
    }

    pub struct BigNatBitDecompParams {
        pub limb_width: usize,
        pub n_limbs: usize,
    }

    pub struct BigNatBitDecomp {
        inputs: Option<BigNatBitDecompInputs>,
        params: BigNatBitDecompParams,
    }

    impl<Scalar: PrimeField> Circuit<Scalar> for BigNatBitDecomp {
        fn synthesize<CS: ConstraintSystem<Scalar>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let n = BigNat::alloc_from_nat(
                cs.namespace(|| "n"),
                || Ok(self.inputs.grab()?.n.clone()),
                self.params.limb_width,
                self.params.n_limbs,
            )?;
            n.decompose(cs.namespace(|| "decomp"))?;
            Ok(())
        }
    }

    #[quickcheck]
    fn big_nat_can_decompose(n: u32, limb_width: u8) -> TestResult {
        use crate::util::scalar::Fr;
        let n = n as usize;
        if limb_width < 4 || limb_width > 200 {
            return TestResult::discard();
        }
        let n_limbs = if n == 0 {
            1
        } else {
            (n - 1) / limb_width as usize + 1
        };

        let circuit = BigNatBitDecomp {
            inputs: Some(BigNatBitDecompInputs {
                n: Integer::from(n),
            }),
            params: BigNatBitDecompParams {
                limb_width: limb_width as usize,
                n_limbs,
            },
        };
        let mut cs = TestConstraintSystem::<Fr>::new();
        circuit.synthesize(&mut cs).expect("synthesis failed");
        TestResult::from_bool(cs.is_satisfied())
    }
}

impl<Scalar: PrimeField> Display for BigNat<Scalar> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.value.as_ref() {
            Some(n) => write!(f, "BigNat({})", n),
            None => write!(f, "BigNat(empty)"),
        }
    }
}

impl Debug for BigNatParams {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("BigNatParams")
            .field("limb_width", &self.limb_width)
            .field("n_limbs", &self.n_limbs)
            .field("min_bits", &self.min_bits)
            .field("max_word", &format_args!("{}", &self.max_word))
            .finish()
    }
}

impl<Scalar: PrimeField> Debug for BigNat<Scalar> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("BigNat")
            .field("params", &self.params)
            .field("limb_values", &self.limb_values)
            .field("value", &format_args!("{}", &self))
            .finish()
    }
}
