use crate as creusot_contracts;
use crate::{logic::OrdLogic, Int, Model};
use creusot_contracts_proc::*;

/// Adds specifications for checked, wrapping, saturating, and overflowing operations on the given
/// integer type
macro_rules! spec_type {
    ($type:ty) => {
        spec_op!($type, +, checked_add, wrapping_add, saturating_add, overflowing_add);
        spec_op!($type, -, checked_sub, wrapping_sub, saturating_sub, overflowing_sub);
        spec_op!($type, *, checked_mul, wrapping_mul, saturating_mul, overflowing_mul);
        spec_op!($type, /, checked_div, wrapping_div, saturating_div, overflowing_div);
    };
}

/// Adds specifications for checked, wrapping, saturating, and overflowing versions of the given
/// operation on the given type
macro_rules! spec_op {
    (
        $type:ty,
        $op:tt,
        $checked:ident,
        $wrapping:ident,
        $saturating:ident,
        $overflowing:ident $(,)?
    ) => {
        extern_spec! {
            impl $type {
                // Checked: performs the operation on `Int`, returns `Some` if the result is between
                // `$type::MIN` and `$type::MAX`, or `None` if the result cannot be represented by
                // `$type`
                #[allow(dead_code)]
                #[ensures(
                    (result == None)
                    == ((@self $op @rhs) < @$type::MIN || (@self $op @rhs) > @$type::MAX)
                )]
                #[ensures(forall<r: $type> result == Some(r) ==> @r == (@self $op @rhs))]
                fn $checked(self, rhs: $type) -> Option<$type>;

                // Wrapping: performs the operation on `Int` and converts back to `$type`
                #[allow(dead_code)]
                #[ensures(
                    @result == (@self $op @rhs).rem_euclid(2.pow(@$type::BITS)) + @$type::MIN
                )]
                fn $wrapping(self, rhs: $type) -> $type;

                // Saturating: performs the operation on `Int` and clamps the result between
                // `$type::MIN` and `$type::MAX`
                #[allow(dead_code)]
                #[ensures(
                    (@self $op @rhs) >= @$type::MIN && (@self $op @rhs) <= @$type::MAX
                    ==> @result == (@self $op @rhs)
                )]
                #[ensures((@self $op @rhs) < @$type::MIN ==> @result == @$type::MIN)]
                #[ensures((@self $op @rhs) > @$type::MAX ==> @result == @$type::MAX)]
                fn $saturating(self, rhs: $type) -> $type;

                // Overflowing: performs the operation on `Int` and converts back to `$type`, and
                // indicates whether an overflow occurred
                #[allow(dead_code)]
                #[ensures(
                    @result.0 == (@self $op @rhs).rem_euclid(2.pow(@$type::BITS)) + @$type::MIN
                )]
                #[ensures(
                    @result.1 == ((@self $op @rhs) < @$type::MIN || (@self $op @rhs) > @$type::MAX)
                )]
                fn $overflowing(self, rhs: $type) -> ($type, bool);
            }
        }
    };
}

spec_type!(u8);
spec_type!(u16);
spec_type!(u32);
spec_type!(u64);
spec_type!(u128);
spec_type!(usize);

spec_type!(i8);
spec_type!(i16);
spec_type!(i32);
spec_type!(i64);
spec_type!(i128);
spec_type!(isize);
