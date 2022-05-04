use byteorder::WriteBytesExt;
use ff::PrimeField;
use num_bigint::{BigInt, Sign};
use std::io::{self, Write};

fn write_be<F: PrimeField, W: Write>(f: &F, mut writer: W) -> io::Result<()> {
    for digit in f.to_repr().as_ref().iter().rev() {
        writer.write_u8(*digit)?;
    }

    Ok(())
}

/// Convert a field element to a natural number
pub fn f_to_nat<Scalar: PrimeField>(f: &Scalar) -> BigInt {
    let mut s = Vec::new();
    write_be(f, &mut s).unwrap(); // f.to_repr().write_be(&mut s).unwrap();
    BigInt::from_bytes_le(Sign::Plus, f.to_repr().as_ref())
}

/// Convert a natural number to a field element.
/// Returns `None` if the number is too big for the field.
pub fn nat_to_f<Scalar: PrimeField>(n: &BigInt) -> Option<Scalar> {
    Scalar::from_str_vartime(&format!("{}", n))
}

/// Convert a `usize` to a field element.
/// Panics if the field is too small.
pub fn usize_to_f<Scalar: PrimeField>(n: usize) -> Scalar {
    // Scalar::from_repr(<Scalar::Repr as From<u64>>::from(n as u64)).expect("decoding problem")
    Scalar::from(n as u64)
}

/// Convert a `usize` to a field element.
/// Panics if the field is too small.
pub fn f_to_usize<Scalar: PrimeField>(n: &Scalar) -> usize {
    let s = n.to_repr();
    assert!(s.as_ref().iter().skip(1).all(|v| *v == 0));
    s.as_ref()[0] as usize
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::util::scalar::Fr;
    use ff::PrimeField;

    #[test]
    fn test_nat_to_f() {
        let n = BigInt::from(4usize);
        let e = Fr::from_str_vartime("4").unwrap();
        assert!(nat_to_f::<Fr>(&n).unwrap() == e);
    }

    #[test]
    fn test_f_to_nat() {
        let n = BigInt::from(4usize);
        let e = Fr::from_str_vartime("4").unwrap();
        assert!(f_to_nat(&e) == n)
    }

    #[test]
    fn test_usize_to_f() {
        let n = 4usize;
        let e = Fr::from_str_vartime("4").unwrap();
        assert!(usize_to_f::<Fr>(n) == e);
    }

    #[test]
    fn test_f_to_usize() {
        let n = 4usize;
        let e = Fr::from_str_vartime("4").unwrap();
        assert!(f_to_usize(&e) == n)
    }
}
