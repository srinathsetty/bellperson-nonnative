use bellperson::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::PrimeField;

use std::cmp::max;
use std::fmt::{self, Debug, Formatter};

use crate::OptionExt;

pub struct Polynomial<Scalar: PrimeField> {
    pub coefficients: Vec<LinearCombination<Scalar>>,
    pub values: Option<Vec<Scalar>>,
}

impl<Scalar: PrimeField> Debug for Polynomial<Scalar> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("Polynomial")
            .field("values", &self.values)
            .finish()
    }
}

impl<Scalar: PrimeField> Polynomial<Scalar> {
    pub fn evaluate_at(&self, x: Scalar) -> Option<Scalar> {
        self.values.as_ref().map(|vs| {
            let mut v = Scalar::ONE;
            let mut acc = Scalar::ZERO;
            for coeff in vs {
                let mut t = coeff.clone();
                t.mul_assign(&v);
                acc.add_assign(&t);
                v.mul_assign(&x);
            }
            acc
        })
    }
    pub fn alloc_product<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Polynomial<Scalar>, SynthesisError> {
        let n_product_coeffs = self.coefficients.len() + other.coefficients.len() - 1;
        let values = self.values.as_ref().and_then(|self_vs| {
            other.values.as_ref().map(|other_vs| {
                let mut values: Vec<Scalar> = std::iter::repeat_with(|| Scalar::ZERO)
                    .take(n_product_coeffs)
                    .collect();
                for (self_i, self_v) in self_vs.iter().enumerate() {
                    for (other_i, other_v) in other_vs.iter().enumerate() {
                        let mut v = self_v.clone();
                        v.mul_assign(other_v);
                        values[self_i + other_i].add_assign(&v);
                    }
                }
                values
            })
        });
        let coefficients = (0..n_product_coeffs)
            .map(|i| {
                Ok(LinearCombination::zero()
                    + cs.alloc(|| format!("prod {}", i), || Ok(values.grab()?[i].clone()))?)
            })
            .collect::<Result<Vec<LinearCombination<Scalar>>, SynthesisError>>()?;
        let product = Polynomial {
            coefficients,
            values,
        };
        let one = Scalar::ONE;
        let mut x = Scalar::ZERO;
        for _ in 1..(n_product_coeffs + 1) {
            x.add_assign(&one);
            cs.enforce(
                || format!("pointwise product @ {:?}", x),
                |lc| {
                    let mut i = Scalar::ONE;
                    self.coefficients.iter().fold(lc, |lc, c| {
                        let r = lc + (i, c);
                        i.mul_assign(&x);
                        r
                    })
                },
                |lc| {
                    let mut i = Scalar::ONE;
                    other.coefficients.iter().fold(lc, |lc, c| {
                        let r = lc + (i, c);
                        i.mul_assign(&x);
                        r
                    })
                },
                |lc| {
                    let mut i = Scalar::ONE;
                    product.coefficients.iter().fold(lc, |lc, c| {
                        let r = lc + (i, c);
                        i.mul_assign(&x);
                        r
                    })
                },
            )
        }
        Ok(product)
    }

    pub fn sum(&self, other: &Self) -> Self {
        let n_coeffs = max(self.coefficients.len(), other.coefficients.len());
        let values = self.values.as_ref().and_then(|self_vs| {
            other.values.as_ref().map(|other_vs| {
                (0..n_coeffs)
                    .map(|i| {
                        let mut s = Scalar::ZERO;
                        if i < self_vs.len() {
                            s.add_assign(&self_vs[i]);
                        }
                        if i < other_vs.len() {
                            s.add_assign(&other_vs[i]);
                        }
                        s
                    })
                    .collect()
            })
        });
        let coefficients = (0..n_coeffs)
            .map(|i| {
                let mut lc = LinearCombination::zero();
                if i < self.coefficients.len() {
                    lc = lc + &self.coefficients[i];
                }
                if i < other.coefficients.len() {
                    lc = lc + &other.coefficients[i];
                }
                lc
            })
            .collect();
        Polynomial {
            coefficients,
            values,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::convert::usize_to_f;
    use crate::util::scalar::Fr;
    use bellperson::gadgets::test::TestConstraintSystem;
    use bellperson::Circuit;

    pub struct PolynomialMultiplier<Scalar: PrimeField> {
        pub a: Vec<Scalar>,
        pub b: Vec<Scalar>,
    }

    impl<Scalar: PrimeField> Circuit<Scalar> for PolynomialMultiplier<Scalar> {
        fn synthesize<CS: ConstraintSystem<Scalar>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let a = Polynomial {
                coefficients: self
                    .a
                    .iter()
                    .enumerate()
                    .map(|(i, x)| {
                        Ok(LinearCombination::zero()
                            + cs.alloc(|| format!("coeff_a {}", i), || Ok(*x))?)
                    })
                    .collect::<Result<Vec<LinearCombination<Scalar>>, SynthesisError>>()?,
                values: Some(self.a),
            };
            let b = Polynomial {
                coefficients: self
                    .b
                    .iter()
                    .enumerate()
                    .map(|(i, x)| {
                        Ok(LinearCombination::zero()
                            + cs.alloc(|| format!("coeff_b {}", i), || Ok(*x))?)
                    })
                    .collect::<Result<Vec<LinearCombination<Scalar>>, SynthesisError>>()?,
                values: Some(self.b),
            };
            let _prod = Polynomial::from(a)
                .alloc_product(cs.namespace(|| "product"), &Polynomial::from(b))?;
            Ok(())
        }
    }

    #[test]
    fn test_circuit() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let circuit = PolynomialMultiplier {
            a: [1, 1, 1].iter().map(|i| usize_to_f::<Fr>(*i)).collect(),
            b: [1, 1].iter().map(|i| usize_to_f::<Fr>(*i)).collect(),
        };

        circuit.synthesize(&mut cs).expect("synthesis failed");

        if let Some(token) = cs.which_is_unsatisfied() {
            eprintln!("Error: {} is unsatisfied", token);
        }
    }
}
