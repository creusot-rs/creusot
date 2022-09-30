use crate as creusot_contracts;
use crate::Int;
use creusot_contracts_proc::*;

/// Adds specifications for checked, wrapping, saturating, and overflowing operations on the given
/// integer type
macro_rules! spec_type {
    ($type:ty) => {
        // Specify addition, subtraction and multiplication
        spec_op_common!($type, +, checked_add, wrapping_add, saturating_add, overflowing_add);
        spec_op_common!($type, -, checked_sub, wrapping_sub, saturating_sub, overflowing_sub);
        spec_op_common!($type, *, checked_mul, wrapping_mul, saturating_mul, overflowing_mul);

        // Specify division separately, because it has the additional precondition that the divisor
        // is non-zero. Overflow on division can only occur on signed types and only when computing
        // `$type::MIN / -1`.
        extern_spec! {
            impl $type {
                #[allow(dead_code)]
                // Returns `None` iff the divisor is zero or the division overflows
                #[ensures((result == None) == (@rhs == 0 || (@self == @$type::MIN && @rhs == -1)))]
                // Else, returns the result of the division
                #[ensures(forall<r: $type> result == Some(r) ==> @r == @self / @rhs)]
                fn checked_div(self, rhs: $type) -> Option<$type>;

                #[allow(dead_code)]
                // Panics if the divisor is zero
                #[requires(@rhs != 0)]
                // Returns `self` if the division overflows
                #[ensures((@self == @$type::MIN && @rhs == -1) ==> @result == @self)]
                // Else, returns the result of the division
                #[ensures((@self == @$type::MIN && @rhs == -1) || @result == @self / @rhs)]
                fn wrapping_div(self, rhs: $type) -> $type;

                #[allow(dead_code)]
                // Panics if the divisor is zero
                #[requires(@rhs != 0)]
                // Returns `$type::MIN` if the division overflows
                #[ensures((@self == @$type::MIN && @rhs == -1) ==> @result == @$type::MIN)]
                // Else, returns the result of the division
                #[ensures((@self == @$type::MIN && @rhs == -1) || @result == @self / @rhs)]
                fn saturating_div(self, rhs: $type) -> $type;

                #[allow(dead_code)]
                // Panics if the divisor is zero
                #[requires(@rhs != 0)]
                // Returns `self` if the division overflows
                #[ensures((@self == @$type::MIN && @rhs == -1) ==> @result.0 == @self)]
                // Else, returns the result of the division
                #[ensures((@self == @$type::MIN && @rhs == -1) || @result.0 == @self / @rhs)]
                // Overflow only occurs when computing `$type::MIN / -1`
                #[ensures(result.1 == (@self == @$type::MIN && @rhs == -1))]
                fn overflowing_div(self, rhs: $type) -> ($type, bool);
            }
        }
    };
}

/// Adds specifications for checked, wrapping, saturating, and overflowing versions of the given
/// operation on the given type. This only works for operations that have no additional pre- or
/// postconditions.
macro_rules! spec_op_common {
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
                // Returns `None` iff the result is out of range
                #[ensures(
                    (result == None)
                    == ((@self $op @rhs) < @$type::MIN || (@self $op @rhs) > @$type::MAX)
                )]
                // Returns `Some(result)` if the result is in range
                #[ensures(forall<r: $type> result == Some(r) ==> @r == (@self $op @rhs))]
                fn $checked(self, rhs: $type) -> Option<$type>;

                // Wrapping: performs the operation on `Int` and converts back to `$type`
                #[allow(dead_code)]
                // Returns result converted to `$type`
                #[ensures(
                    @result == (@self $op @rhs).rem_euclid(2.pow(@$type::BITS)) + @$type::MIN
                )]
                // Returns the result if it is in range
                #[ensures(
                    (@self $op @rhs) >= @$type::MIN && (@self $op @rhs) <= @$type::MAX
                    ==> @result == (@self $op @rhs)
                )]
                // Returns the result shifted by a multiple of the type's range if it is out of
                // range. For addition and subtraction, `k` (qualified over below) will always be 1
                // or -1, but the verifier is able to deduce that.
                #[ensures(
                    (@self $op @rhs) < @$type::MIN
                    ==> exists<k: Int> k > 0
                        && @result == (@self $op @rhs) + k * (@$type::MAX - @$type::MIN + 1)
                )]
                #[ensures(
                    (@self $op @rhs) > @$type::MAX
                    ==> exists<k: Int> k > 0
                        && @result == (@self $op @rhs) - k * (@$type::MAX - @$type::MIN + 1)
                )]
                fn $wrapping(self, rhs: $type) -> $type;

                // Saturating: performs the operation on `Int` and clamps the result between
                // `$type::MIN` and `$type::MAX`
                #[allow(dead_code)]
                // Returns the result if it is in range
                #[ensures(
                    (@self $op @rhs) >= @$type::MIN && (@self $op @rhs) <= @$type::MAX
                    ==> @result == (@self $op @rhs)
                )]
                // Returns the nearest bound if the result is out of range
                #[ensures((@self $op @rhs) < @$type::MIN ==> @result == @$type::MIN)]
                #[ensures((@self $op @rhs) > @$type::MAX ==> @result == @$type::MAX)]
                fn $saturating(self, rhs: $type) -> $type;

                // Overflowing: performs the operation on `Int` and converts back to `$type`, and
                // indicates whether an overflow occurred
                #[allow(dead_code)]
                // Returns result converted to `$type`
                #[ensures(
                    @result.0 == (@self $op @rhs).rem_euclid(2.pow(@$type::BITS)) + @$type::MIN
                )]
                // Returns the result if it is in range
                #[ensures(
                    (@self $op @rhs) >= @$type::MIN && (@self $op @rhs) <= @$type::MAX
                    ==> @result.0 == (@self $op @rhs)
                )]
                // Returns the result shifted by a multiple of the type's range if it is out of
                // range. For addition and subtraction, `k` (qualified over below) will always be 1
                // or -1, but the verifier is able to deduce that.
                #[ensures(
                    (@self $op @rhs) < @$type::MIN
                    ==> exists<k: Int> k > 0
                        && @result.0 == (@self $op @rhs) + k * (@$type::MAX - @$type::MIN + 1)
                )]
                #[ensures(
                    (@self $op @rhs) > @$type::MAX
                    ==> exists<k: Int> k > 0
                        && @result.0 == (@self $op @rhs) - k * (@$type::MAX - @$type::MIN + 1)
                )]
                // Overflow occurred iff the result is out of range
                #[ensures(
                    result.1 == ((@self $op @rhs) < @$type::MIN || (@self $op @rhs) > @$type::MAX)
                )]
                fn $overflowing(self, rhs: $type) -> ($type, bool);
            }
        }
    };
}

/// Adds specifications for the abs_diff operation on the given pair of signed
/// and unsigned integer types
macro_rules! spec_abs_diff {
    ($unsigned:ty, $signed:ty) => {
        extern_spec! {
            impl $unsigned {
                #[allow(dead_code)]
                #[ensures(@result == (@self).abs_diff(@other))]
                fn abs_diff(self, other: $unsigned) -> $unsigned;
            }

            impl $signed {
                #[allow(dead_code)]
                #[ensures(@result == (@self).abs_diff(@other))]
                fn abs_diff(self, other: $signed) -> $unsigned;
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

spec_abs_diff!(u8, i8);
spec_abs_diff!(u16, i16);
spec_abs_diff!(u32, i32);
spec_abs_diff!(u64, i64);
spec_abs_diff!(u128, i128);
spec_abs_diff!(usize, isize);
