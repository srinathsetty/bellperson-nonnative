pub use bellpepper_core::test_cs::TestConstraintSystem;
pub use bellpepper_core::Circuit;
pub use ff::PrimeField;

macro_rules! circuit_tests {
    ($($name:ident: $value:expr,)*) => {
        $(
            #[test]
            fn $name() {
                use crate::util::scalar::Fr;
                let (circuit, is_sat) = $value;
                let mut cs = TestConstraintSystem::<Fr>::new();

                circuit.synthesize(&mut cs).expect("synthesis failed");
                println!(concat!("Constraints in {}: {}"), stringify!($name), cs.num_constraints());
                if is_sat && !cs.is_satisfied() {
                    println!("UNSAT: {:#?}", cs.which_is_unsatisfied())
                }
                assert_eq!(cs.is_satisfied(), is_sat);
            }
        )*
    }
}
