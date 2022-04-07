use bellperson::gadgets::num::AllocatedNum;
use bellperson::{ConstraintSystem, LinearCombination, SynthesisError, Variable};
use ff::PrimeField;

use super::bit::{Bit, Bitvector};
use std::convert::From;
use BitAccess;
use OptionExt;

pub struct Num<Scalar: PrimeField> {
    pub num: LinearCombination<Scalar>,
    pub value: Option<Scalar>,
}

impl<Scalar: PrimeField> Num<Scalar> {
    pub fn new(value: Option<Scalar>, num: LinearCombination<Scalar>) -> Self {
        Self { value, num }
    }
    pub fn alloc<CS, F>(mut cs: CS, value: F) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
        F: FnOnce() -> Result<Scalar, SynthesisError>,
    {
        let mut new_value = None;
        let var = cs.alloc(
            || "num",
            || {
                let tmp = value()?;

                new_value = Some(tmp);

                Ok(tmp)
            },
        )?;

        Ok(Num {
            value: new_value,
            num: LinearCombination::zero() + var,
        })
    }

    pub fn fits_in_bits<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        n_bits: usize,
    ) -> Result<(), SynthesisError> {
        let v = self.value.map(|v| v);

        // Allocate all but the first bit.
        let bits: Vec<Variable> = (1..n_bits)
            .map(|i| {
                cs.alloc(
                    || format!("bit {}", i),
                    || {
                        let r = if *v.grab()?.get_bit(i).grab()? {
                            Scalar::one()
                        } else {
                            Scalar::zero()
                        };
                        Ok(r)
                    },
                )
            })
            .collect::<Result<_, _>>()?;

        for (i, v) in bits.iter().enumerate() {
            cs.enforce(
                || format!("{} is bit", i),
                |lc| lc + v.clone(),
                |lc| lc + CS::one() - v.clone(),
                |lc| lc,
            )
        }

        // Last bit
        cs.enforce(
            || "last bit",
            |mut lc| {
                let mut f = Scalar::one();
                lc = lc + &self.num;
                for v in bits.iter() {
                    f = f.double();
                    lc = lc - (f, *v);
                }
                lc
            },
            |mut lc| {
                lc = lc + CS::one();
                let mut f = Scalar::one();
                lc = lc - &self.num;
                for v in bits.iter() {
                    f = f.double();
                    lc = lc + (f, *v);
                }
                lc
            },
            |lc| lc,
        );
        Ok(())
    }

    /// Computes the natural number represented by an array of bits.
    /// Checks if the natural number equals `self`
    pub fn is_equal<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Bitvector<Scalar>,
    ) -> Result<(), SynthesisError> {
        let allocations = other.allocations.clone();
        let mut f = Scalar::one();
        let sum = allocations
            .iter()
            .fold(LinearCombination::zero(), |lc, bit| {
                let l = lc + (f, &bit.bit);
                f = f.double();
                l
            });
        let sum_lc = LinearCombination::zero() + &self.num - &sum_of_tail_bits;
        cs.enforce(|| "sum", |lc| lc + &sum_lc, |lc| lc + CS::one(), |lc| lc);
        Ok(())
    }

    /// Compute the natural number represented by an array of limbs.
    /// The limbs are assumed to be based the `limb_width` power of 2.
    /// Low-index bits are low-order
    pub fn decompose<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        n_bits: usize,
    ) -> Result<Bitvector<Scalar>, SynthesisError> {
        let values: Option<Vec<bool>> = self.value.as_ref().map(|v| {
            let num = v.clone();
            (0..n_bits)
                .map(|i| {
                    let bit = num.get_bit(i).unwrap();
                    bit
                })
                .collect()
        });
        let allocations: Vec<Bit<Scalar>> = (0..n_bits)
            .map(|bit_i| {
                Bit::alloc(
                    cs.namespace(|| format!("bit{}", bit_i)),
                    values.as_ref().map(|vs| vs[bit_i]),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut f = Scalar::one();
        let sum_of_tail_bits = allocations
            .iter()
            .fold(LinearCombination::zero(), |lc, bit| {
                let l = lc + (f, &bit.bit);
                f = f.double();
                l
            });
        let sum_lc = LinearCombination::zero() + &self.num - &sum_of_tail_bits;
        cs.enforce(|| "sum", |lc| lc + &sum_lc, |lc| lc + CS::one(), |lc| lc);
        let bits: Vec<LinearCombination<Scalar>> = allocations
            .clone()
            .into_iter()
            .map(|a| LinearCombination::zero() + &a.bit)
            .collect();
        Ok(Bitvector {
            allocations,
            values,
            bits,
        })
    }

    pub fn as_sapling_allocated_num<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
    ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
        let new = AllocatedNum::alloc(cs.namespace(|| "alloc"), || Ok(*self.value.grab()?))?;
        cs.enforce(
            || "eq",
            |lc| lc,
            |lc| lc,
            |lc| lc + new.get_variable() - &self.num,
        );
        Ok(new)
    }
}

impl<Scalar: PrimeField> From<AllocatedNum<Scalar>> for Num<Scalar> {
    fn from(a: AllocatedNum<Scalar>) -> Self {
        Self::new(a.get_value(), LinearCombination::zero() + a.get_variable())
    }
}
