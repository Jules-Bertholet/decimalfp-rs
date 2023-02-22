//! Decimal floating point arithmetic in Rust, using the
//! [Intel Decimal Floating-Point Math Library](https://www.intel.com/content/www/us/en/developer/articles/tool/intel-decimal-floating-point-math-library.html).
//! 
//! Conforms to the IEEE 754-2019 decimal floating point standard.
//! 
//! # Example
//! 
//! ```
//! use decimalfp::prelude::*;
//! 
//! let a = d64!(1.0);
//! let b = d64!(4.7);
//! 
//! let result = a * powi(b, 2);
//! ```

#![forbid(unsafe_op_in_unsafe_fn)]
#![warn(
    missing_docs,
    missing_debug_implementations,
    unused_crate_dependencies
    /*clippy::cargo*/
)]
#![no_std]

extern crate alloc;

use alloc::{
    borrow::ToOwned,
    ffi::CString,
    string::{String, ToString},
};
use bitflags::bitflags;
use core::{
    cmp::Ordering,
    convert::Infallible,
    ffi::{c_char, CStr},
    fmt,
    iter::{Product, Sum},
    mem::MaybeUninit,
    num::FpCategory,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign},
    ptr,
    str::FromStr,
};
use decimalfp_macros_support::replace;
use forward_ref::{forward_ref_binop, forward_ref_op_assign, forward_ref_unop};
use paste::paste;

#[allow(clippy::wildcard_imports)]
use inteldfp_sys::*;

mod private {
    pub trait Sealed {}
}

cfg_if::cfg_if! {
    if #[cfg(target_pointer_width = "16")] {
        type UsizeEquiv = u16;
        type IsizeEquiv = u16;
    } else if #[cfg(target_pointer_width = "32")] {
        type UsizeEquiv = u32;
        type IsizeEquiv = i32;
    } else if #[cfg(target_pointer_width = "64")] {
        type UsizeEquiv = u64;
        type IsizeEquiv = i64;
    } else if #[cfg(target_pointer_width = "128")] {
        type UsizeEquiv = u128;
        type IsizeEquiv = i128;
    }
}

/// Rounding mode for operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum Rounding {
    /// The default rounding mode, and also the most "fair".
    /// Rounds to the nearest number, breaking ties by rounding
    /// to the even number.
    TiesToEven = BID_ROUNDING_TO_NEAREST,

    /// Rounds to the nearest number, breaking ties by rounding away from 0.
    /// The rounding you perhaps learned in school.
    TiesToAway = BID_ROUNDING_TIES_AWAY,

    /// Always round toward positive infinity.
    TowardPositive = BID_ROUNDING_UP,

    /// Always round toward negative infinity.
    TowardNegative = BID_ROUNDING_DOWN,

    /// Always round toward zero.
    TowardZero = BID_ROUNDING_TO_ZERO,
}

impl Default for Rounding {
    #[inline]
    fn default() -> Self {
        Self::TiesToEven
    }
}

impl Rounding {
    fn as_repr(self) -> _IDEC_round {
        self as _IDEC_round
    }
}

/// Ranges that a floating-point number can fall into.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(i32)]
pub enum Class {
    // values from `bid_internal.h` `enum class_types`
    /// A signaling NaN.
    SignalingNan = 0,

    /// A quiet NaN.
    QuietNan = 1,

    /// Negative infinity.
    NegativeInfinite = 2,

    /// A non-subnormal real number less than 0.
    NegativeNormal = 3,

    /// A negative subnormal real number.
    NegativeSubnormal = 4,

    /// Negative zero.
    NegativeZero = 5,

    /// Positive zero.
    PositiveZero = 6,

    /// A positive subnormal real number.
    PositiveSubnormal = 7,

    /// A normal real number greater than 0.
    PositiveNormal = 8,

    /// Positive infinity.
    PositiveInfinite = 9,
}

impl From<Class> for FpCategory {
    fn from(class: Class) -> Self {
        match class {
            Class::SignalingNan | Class::QuietNan => FpCategory::Nan,
            Class::NegativeInfinite | Class::PositiveInfinite => FpCategory::Infinite,
            Class::NegativeNormal | Class::PositiveNormal => FpCategory::Normal,
            Class::NegativeSubnormal | Class::PositiveSubnormal => FpCategory::Subnormal,
            Class::NegativeZero | Class::PositiveZero => FpCategory::Zero,
        }
    }
}

pub mod context {
    //! Defines the [`Context`] struct, which stores the current rounding mode
    //! and floating-point flags. You don't need to use this struct for most operations,
    //! unless you want to use a non-default rounding mode or care about flags.
    //! If you do care about these things, operate on decimals using the methods of [`Context`].

    use super::*;

    /// Stores the current rounding mode and floating-point flags.
    #[derive(Clone, Debug, Default)]
    pub struct Context {
        pub(super) rounding: Rounding,
        pub(super) flags: Flags,
    }

    impl Context {
        /// Create a new `Context` with no flags set and ties-to-even rounding.
        #[must_use]
        #[inline]
        pub const fn new() -> Self {
            Self {
                flags: Flags::empty(),
                rounding: Rounding::TiesToEven,
            }
        }

        /// Create a new `Context` with no flags set and the specified rounding mode.
        #[must_use]
        #[inline]
        pub const fn new_with_rounding(rounding: Rounding) -> Self {
            Self {
                flags: Flags::empty(),
                rounding,
            }
        }

        // TODO the IEEE flags api is not the best, expose an alternative?

        /// IEEE 754 5.7.4 **lowerFlags**
        #[doc(alias = "lowerFlags")]
        #[inline]
        pub fn lower_flags(&mut self, flags: Flags) {
            unsafe { __bid_lowerFlags(flags.bits(), self.flags.as_mut_ptr()) }
        }

        /// IEEE 754 5.7.4 **raiseFlags**
        #[doc(alias = "raiseFlags")]
        #[inline]
        pub fn raise_flags(&mut self, flags: Flags) {
            self.flags = self.flags.union(flags);
        }

        /// IEEE 754 5.7.4 **testFlags**
        #[doc(alias = "testFlags")]
        #[must_use]
        #[inline]
        pub fn test_flags(&self, flags: Flags) -> Flags {
            unsafe {
                Flags::from_bits_unchecked(__bid_testFlags(
                    flags.bits(),
                    self.flags.as_ptr() as *mut _IDEC_flags,
                ))
            }
        }

        /// IEEE 754 5.7.4 **restoreFlags**
        #[doc(alias = "restoreFlags")]
        #[inline]
        pub fn restore_flags(&mut self, flags: Flags, mask: Flags) {
            unsafe { __bid_restoreFlags(flags.bits(), mask.bits(), self.flags.as_mut_ptr()) }
        }

        /*
        #[must_use]
        #[inline]
        pub fn save_flags(&mut self, mask: Flags) -> Flags {
            unsafe {
                Flags::from_bits_unchecked(__bid_saveFlags(mask.bits(), self.flags.as_mut_ptr()))
            }
        }
        */

        /// IEEE 754 5.7.4 **saveAllFlags**
        #[doc(alias = "saveAllFlags")]
        #[must_use]
        #[inline]
        pub fn save_all_flags(&mut self) -> Flags {
            unsafe {
                Flags::from_bits_unchecked(__bid_saveFlags(
                    Flags::all().bits(),
                    self.flags.as_mut_ptr(),
                ))
            }
        }

        /// IEEE 754 9.3.1 **getDecimalRoundingDirection**
        #[doc(alias = "getDecimalRoundingDirection")]
        #[must_use]
        #[inline]
        pub const fn get_rounding(&self) -> Rounding {
            self.rounding
        }

        /// IEEE 754 9.3.1 **setDecimalRoundingDirection**
        #[doc(alias = "setDecimalRoundingDirection")]
        #[inline]
        pub fn set_rounding(&mut self, round: Rounding) {
            self.rounding = round;
        }
    }

    bitflags! {
        #[derive(Default)]
        /// IEEE 754 section 7
        pub struct Flags: _IDEC_flags {
            /// IEEE 754 7.2
            const INVALID_OPERATION = DEC_FE_INVALID;
            /// A non-normal float was encountered.
            const DENORMAL = DEC_FE_UNNORMAL;
            /// IEEE 754 7.3
            const DIVISION_BY_ZERO = DEC_FE_DIVBYZERO;
            /// IEEE 754 7.4
            const OVERFLOW = DEC_FE_OVERFLOW;
            /// IEEE 754 7.5
            const UNDERFLOW = DEC_FE_UNDERFLOW;
            /// IEEE 754 7.6
            const INEXACT = DEC_FE_INEXACT;
        }
    }

    impl Flags {
        // FIXME is this useful?
        /// IEEE 754 5.7.4 **testSavedFlags**
        ///
        /// Equivalent to `intersection`.
        #[doc(alias = "testSavedFlags")]
        #[must_use]
        #[inline]
        pub fn test_saved_flags(self, flags: Flags) -> Flags {
            unsafe { Flags::from_bits_unchecked(__bid_testSavedFlags(self.bits(), flags.bits())) }
        }

        pub(super) fn as_ptr(self) -> *const _IDEC_flags {
            ptr::addr_of!(self.bits)
        }

        pub(super) fn as_mut_ptr(&mut self) -> *mut _IDEC_flags {
            ptr::addr_of_mut!(self.bits)
        }
    }

    macro_rules! ctx {
        (
            impl Context where XX = <$($x:literal),+> $tt:tt
        ) => {
            ctx_def!(impl Context $tt);

            $(ctx_impl!(impl Decimal for $x $tt);)+
        };
    }

    macro_rules! ctx_def {
        (impl Context { $(
            $(#[$attr:meta])*
            pub $([$tt:ident])? fn $fn_name:ident($ctx:ident: &mut Context $(, $arg:ident : $arg_ty:ty)*) $(-> $fn_ret:ty)? {
                $($impl:tt)*
            }
        )*}) => {

            /// Trait implemented by all decimal floating-point types.
            pub trait Decimal: private::Sealed { replace! { DecimalXX, Self, $(
                #[doc(hidden)]
                fn $fn_name($ctx: &mut Context $(, $arg : $arg_ty)*) $(-> $fn_ret)?;
            )*}}

            #[allow(clippy::wrong_self_convention)]
            impl Context { replace! { DecimalXX, D, $(
                $(#[$attr])*
                pub fn $fn_name<DecimalXX: Decimal>(&mut self $(, $arg : $arg_ty)*) $(-> $fn_ret)? {
                    <DecimalXX as Decimal>::$fn_name(self $(, $arg)*)
                }
            )*}}
        };
    }

    macro_rules! ctx_impl {
        (impl Decimal for $x:literal {$(
            $(#[$attr:meta])*
            pub $(fn $fn_name:ident($ctx:ident: &mut Context $(, $arg:ident : $arg_ty:ty)*) $(-> $fn_ret:ty)? {
                $($impl:tt)*
            })?
            $([dec_to_dec] fn $d2d_fn_name:ident($d2d_ctx:ident: &mut Context $(, $d2d_arg:ident : DecimalXX)*) -> DecimalXX {
                $d2d_c_fn:ident
            })?
            $([dec_to_dec_round] fn $d2dr_fn_name:ident($d2dr_ctx:ident: &mut Context $
                (, $d2dr_arg:ident : DecimalXX)*) -> DecimalXX {
                $d2dr_c_fn:ident
            })?
            $([dec_to_bool] fn $d2b_fn_name:ident($d2b_ctx:ident: &mut Context $
                (, $d2b_arg:ident : DecimalXX)*) -> bool {
                $d2b_c_fn:ident
            })?
        )*}) => { paste! {

            impl Decimal for [<Decimal$x>] { replace! { XX, $x, $(
                $(#[$attr])*
                #[inline]
                fn $($fn_name($ctx: &mut Context $(, $arg : $arg_ty)*) $(-> $fn_ret)? {
                    $($impl)*
                })?
                $(
                    $d2d_fn_name($d2d_ctx: &mut Context $(, $d2d_arg: [<Decimal$x>])*) -> [<Decimal$x>] {
                        let inner = unsafe {
                            [<__bid $x _ $d2d_c_fn>]($($d2d_arg.inner, )* $d2d_ctx.flags.as_mut_ptr())
                        };

                        [<Decimal$x>] { inner }
                    }
                )?
                $(
                    $d2dr_fn_name($d2dr_ctx: &mut Context $(, $d2dr_arg: [<Decimal$x>])*) -> [<Decimal$x>] {
                        let inner = unsafe {
                            [<__bid $x _ $d2dr_c_fn>]($($d2dr_arg.inner, )* $d2dr_ctx.rounding.as_repr(), $d2dr_ctx.flags.as_mut_ptr())
                        };

                        [<Decimal$x>] { inner }
                    }
                )?
                $(
                    $d2b_fn_name($d2b_ctx: &mut Context $(, $d2b_arg: [<Decimal$x>])*) -> bool {
                        (unsafe {
                            [<__bid $x _ $d2b_c_fn>]($($d2b_arg.inner, )* $d2b_ctx.flags.as_mut_ptr())
                        }) != 0
                    }
                )?
            )*}}
        }};
    }

    ctx! {
        impl Context where XX = <32, 64, 128> {
            /// IEEE 754 5.3.1 **roundToIntegralTiesToEven**
            #[doc(alias = "roundToIntegralTiesToEven")]
            pub [dec_to_dec] fn round_ties_even(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                round_integral_nearest_even
            }

            /// IEEE 754 5.3.1 **roundToIntegralTiesToAway**
            #[doc(alias = "roundToIntegralTiesToAway")]
            pub [dec_to_dec] fn round(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                round_integral_nearest_away
            }

            /// IEEE 754 5.3.1 **roundToIntegralTowardZero**
            #[doc(alias = "roundToIntegralTowardZero")]
            pub [dec_to_dec] fn trunc(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                round_integral_zero
            }

            /// IEEE 754 5.3.1 **roundToIntegralTowardPositive**
            #[doc(alias = "roundToIntegralTowardPositive")]
            pub [dec_to_dec] fn ceil(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                round_integral_positive
            }

            /// IEEE 754 5.3.1 **roundToIntegralTowardNegative**
            #[doc(alias = "roundToIntegralTowardNegative")]
            pub [dec_to_dec] fn floor(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                round_integral_negative
            }

            // Todo rename?
            /// IEEE 754 5.3.1 **roundToIntegralExact**
            #[doc(alias = "roundToIntegralExact")]
            pub [dec_to_dec_round] fn round_to_integral_exact(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                round_integral_exact
            }

            /// IEEE 754 5.3.1 **nextUp**
            #[doc(alias = "nextUp")]
            pub [dec_to_dec] fn next_up(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                nextup
            }

            /// IEEE 754 5.3.1 **nextDown**
            #[doc(alias = "nextDown")]
            pub [dec_to_dec] fn next_down(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                nextdown
            }

            /// IEEE 754 5.3.1 **remainder**
            ///
            /// Not the same as `rem` or the `%` operator.
            pub [dec_to_dec] fn remainder(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                rem
            }

            // FIXME 2019 minimum?

            /// IEEE 754 5.3.1 **minNum**
            ///
            /// This operation was removed in IEEE 754-2019.
            #[doc(alias = "minNum")]
            pub [dec_to_dec] fn min(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                minnum
            }

            /// IEEE 754 5.3.1 **maxNum**
            ///
            /// This operation was removed in IEEE 754-2019.
            #[doc(alias = "maxNum")]
            pub [dec_to_dec] fn max(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                maxnum
            }

            /// IEEE 754 5.3.1 **minNumMag**
            ///
            /// This operation was removed in IEEE 754-2019.
            #[doc(alias = "minNumMag")]
            pub [dec_to_dec] fn min_mag(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                minnum_mag
            }

            /// IEEE 754 5.3.1 **maxNumMag**
            ///
            /// This operation was removed in IEEE 754-2019.
            #[doc(alias = "maxNumMag")]
            pub [dec_to_dec] fn max_mag(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                maxnum_mag
            }

            /// IEEE 754 5.3.2 **quantize**
            pub [dec_to_dec_round] fn quantize(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                quantize
            }

            // FIXME add 2019 quantum?

            /// IEEE 754 5.3.3 **scaleB**
            #[doc(alias = "scaleB")]
            pub fn scale10(ctx: &mut Context, x: DecimalXX, n: i32) -> DecimalXX {
                let inner = unsafe {
                    __bidXX_scalbn(x.inner, n, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                };

                DecimalXX { inner }
            }

            /// IEEE 754 5.3.3 **logB**
            #[doc(alias = "logB")] // todo logb fn
            pub fn ilog10(ctx: &mut Context, x: DecimalXX) -> i32 {
                unsafe { __bidXX_ilogb(x.inner, ctx.flags.as_mut_ptr()) }
            }

            /// IEEE 754 5.4.1 **squareRoot**
            #[doc(alias = "squareRoot")]
            pub [dec_to_dec_round] fn sqrt(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                sqrt
            }

            /// IEEE 754 5.4.2 **convertFromDecimalCharacter**
            #[doc(alias = "convertFromDecimalCharacter", alias = "strtod")]
            pub fn from_c_str(ctx: &mut Context, str: &CStr) -> DecimalXX {
                let inner = unsafe {
                    __bidXX_from_string(str.as_ptr() as *mut c_char, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                };

                DecimalXX { inner }
            }

            /// IEEE 754 5.4.1 **convertToDecimalCharacter**
            #[doc(alias = "convertToDecimalCharacter")]
            pub fn to_string(ctx: &mut Context, x: DecimalXX) -> String {
                // Make an unitinitalized buffer of $x characters.
                // This should be more than long enough to contain the string.
                const BUFFER_SIZE: usize = if XX == 32 { 14 } else if XX == 64 { 23 } else if XX == 128 { 42 } else { panic!() };
                let mut buffer: [MaybeUninit<c_char>; BUFFER_SIZE] = [MaybeUninit::<_>::uninit(); BUFFER_SIZE];

                // SAFETY: Providing an uninitialized buffer is safe because it is never read from, only written to.
                // The buffer is exactly long enough to contain the longest possible byte string, including null byte at end.
                unsafe {
                    __bidXX_to_string(buffer.as_mut_ptr().cast(), x.inner, ctx.flags.as_mut_ptr());
                }

                let mut i = 0;
                loop {
                    // SAFETY: Even if an empty string is stored in the buffer, at least one byte will be initialized.
                    // And every byte before the first 0 byte should be iniialized.
                    let ith_char = unsafe { buffer[i].assume_init() };
                    if ith_char == 0 {
                        break;
                    }
                    i += 1;
                }

                let init_portion: &[MaybeUninit<c_char>] = &buffer[..i];
                // SAFETY: Transumting between i8 and u8 is safe. We only transmute the initialized subslice of the buffer.
                let str_bytes: &[u8] = unsafe { &*(init_portion as *const _ as *const [u8]) };
                String::from_utf8(str_bytes.to_owned()).unwrap()
            }

            /// IEEE 754 5.6.1 **compareQuietEqual**
            #[doc(alias = "compareQuietEqual")]
            pub [dec_to_bool] fn eq(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_equal
            }

            /// IEEE 754 5.6.1 **compareQuietNotEqual**
            #[doc(alias = "compareQuietNotEqual")]
            pub [dec_to_bool] fn ne(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_not_equal
            }

            /// IEEE 754 5.6.1 **compareSignalingEqual**
            #[doc(alias = "compareSignalingEqual")]
            pub fn signaling_eq(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                if x.is_nan() || y.is_nan() {
                    ctx.flags = ctx.flags.union(Flags::INVALID_OPERATION)
                }
                x == y
            }

            /// IEEE 754 5.6.1 **compareSignalingGreater**
            #[doc(alias = "compareSignalingGreater")]
            pub [dec_to_bool] fn signaling_gt(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                signaling_greater
            }

            /// IEEE 754 5.6.1 **compareSignalingGreaterEqual**
            #[doc(alias = "compareSignalingGreaterEqual")]
            pub [dec_to_bool] fn signaling_ge(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                signaling_greater_equal
            }

            /// IEEE 754 5.6.1 **compareSignalingLess**
            #[doc(alias = "compareSignalingLess")]
            pub [dec_to_bool] fn signaling_lt(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                signaling_less
            }

            /// IEEE 754 5.6.1 **compareSignalingLessEqual**
            #[doc(alias = "compareSignalingLessEqual")]
            pub [dec_to_bool] fn signaling_le(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                signaling_less_equal
            }

            /// IEEE 754 5.6.1 **compareSignalingNotEqual**
            #[doc(alias = "compareSignalingNotEqual")]
            pub fn signaling_ne(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                if x.is_nan() || y.is_nan() {
                    ctx.flags = ctx.flags.union(Flags::INVALID_OPERATION)
                }
                x != y
            }

            /// IEEE 754 5.6.1 **compareSignalingNotGreater**
            #[doc(alias = "compareSignalingNotGreater")]
            pub [dec_to_bool] fn signaling_ng(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                signaling_not_greater
            }

            /// IEEE 754 5.6.1 **compareSignalingLessUnordered**
            #[doc(alias = "compareSignalingLessUnordered")]
            pub [dec_to_bool] fn signaling_lt_unordered(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                signaling_less_unordered
            }

            /// IEEE 754 5.6.1 **compareSignalingNotLess**
            #[doc(alias = "compareSignalingNotLess")]
            pub [dec_to_bool] fn signaling_nl(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                signaling_not_less
            }

            /// IEEE 754 5.6.1 **compareSignalingGreaterUnordered**
            #[doc(alias = "compareSignalingGreaterUnordered")]
            pub [dec_to_bool] fn signaling_gt_unordered(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                signaling_greater_unordered
            }

            /// IEEE 754 5.6.1 **compareQuietGreater**
            #[doc(alias = "compareQuietGreater")]
            pub [dec_to_bool] fn gt(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_greater
            }

            /// IEEE 754 5.6.1 **compareQuietGreaterEqual**
            #[doc(alias = "compareQuietGreaterEqual")]
            pub [dec_to_bool] fn ge(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_greater_equal
            }

            /// IEEE 754 5.6.1 **compareQuietLess**
            #[doc(alias = "compareQuietLess")]
            pub [dec_to_bool] fn lt(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_less
            }

            /// IEEE 754 5.6.1 **compareQuietLessEqual**
            #[doc(alias = "compareQuietLessEqual")]
            pub [dec_to_bool] fn le(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_less_equal
            }

            /// IEEE 754 5.6.1 **compareQuietUnordered**
            #[doc(alias = "compareQuietUnordered")]
            pub [dec_to_bool] fn unordered(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_unordered
            }

            /// IEEE 754 5.6.1 **compareQuietNotGreater**
            #[doc(alias = "compareQuietNotGreater")]
            pub [dec_to_bool] fn ng(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_not_greater
            }

            /// IEEE 754 5.6.1 **compareQuietLessUnordered**
            #[doc(alias = "compareQuietLessUnordered")]
            pub [dec_to_bool] fn lt_unordered(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_less_unordered
            }

            /// IEEE 754 5.6.1 **compareQuietNotLess**
            #[doc(alias = "compareQuietNotLess")]
            pub [dec_to_bool] fn nl(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_not_less
            }

            /// IEEE 754 5.6.1 **compareQuietGreaterUnordered**
            #[doc(alias = "compareQuietGreaterUnordered")]
            pub [dec_to_bool] fn gt_unordered(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_greater_unordered
            }

            /// IEEE 754 5.6.1 **compareQuietOrdered**
            #[doc(alias = "compareQuietOrdered")]
            pub [dec_to_bool] fn ordered(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> bool {
                quiet_ordered
            }

            // Recommended ops
            // FIXME add some more?

            /// IEEE 754 9.2 **exp**
            pub [dec_to_dec_round] fn exp(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                exp
            }

            /// IEEE 754 9.2 **expm1**
            #[doc(alias = "expm1")]
            pub [dec_to_dec_round] fn exp_m1(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                expm1
            }

            /// IEEE 754 9.2 **exp2**
            pub [dec_to_dec_round] fn exp2(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                exp2
            }

            /// IEEE 754 9.2 **exp10**
            pub [dec_to_dec_round] fn exp10(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                exp10
            }

            /// IEEE 754 9.2 **log**
            #[doc(alias = "log")]
            pub [dec_to_dec_round] fn ln(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                log
            }

            /// IEEE 754 9.2 **log2**
            pub [dec_to_dec_round] fn log2(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                log2
            }

            /// IEEE 754 9.2 **log10**
            pub [dec_to_dec_round] fn log10(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                log10
            }

            /// IEEE 754 9.2 **logp1**
            #[doc(alias = "logp1", alias = "log1p")]
            pub [dec_to_dec_round] fn ln_1p(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                log1p
            }

            /// IEEE 754 9.2 **hypot**
            pub [dec_to_dec_round] fn hypot(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                hypot
            }

            /// IEEE 754 9.2 **pow**
            #[doc(alias = "pow")]
            pub [dec_to_dec_round] fn powf(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                pow
            }

            /// IEEE 754 9.2 **sin**
            pub [dec_to_dec_round] fn sin(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                sin
            }

            /// IEEE 754 9.2 **cos**
            pub [dec_to_dec_round] fn cos(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                cos
            }

            /// IEEE 754 9.2 **tan**
            pub [dec_to_dec_round] fn tan(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                tan
            }

            /// IEEE 754 9.2 **asin**
            pub [dec_to_dec_round] fn asin(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                asin
            }

            /// IEEE 754 9.2 **acos**
            pub [dec_to_dec_round] fn acos(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                acos
            }

            /// IEEE 754 9.2 **atan**
            pub [dec_to_dec_round] fn atan(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                atan
            }

            /// IEEE 754 9.2 **atan2**
            pub [dec_to_dec_round] fn atan2(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                atan2
            }

            /// IEEE 754 9.2 **sinh**
            pub [dec_to_dec_round] fn sinh(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                sinh
            }

            /// IEEE 754 9.2 **cosh**
            pub [dec_to_dec_round] fn cosh(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                cosh
            }

            /// IEEE 754 9.2 **tanh**
            pub [dec_to_dec_round] fn tanh(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                tanh
            }

            /// IEEE 754 9.2 **asinh**
            pub [dec_to_dec_round] fn asinh(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                asinh
            }

            /// IEEE 754 9.2 **acosh**
            pub [dec_to_dec_round] fn acosh(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                acosh
            }

            /// IEEE 754 9.2 **atanh**
            pub [dec_to_dec_round] fn atanh(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                atanh
            }

            // Non-IEEE methods

            /// Cube root
            pub [dec_to_dec_round] fn cbrt(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                cbrt
            }

            /// C `erf`
            pub [dec_to_dec_round] fn erf(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                erf
            }

            /// C `erfc`
            pub [dec_to_dec_round] fn erfc(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                erfc
            }

            /// Equivalent to `fdim` in C
            #[doc(alias = "fdim")]
            pub [dec_to_dec_round] fn abs_sub(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                fdim
            }

            /// Equivalent to `fmod` in C, and the `%` operator in Rust.
            /// Not the same as IEEE 754 remainder.
            #[doc(alias = "fmod")]
            pub [dec_to_dec] fn rem(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                fmod
            }

            // FIXME frexp, nexttoward..

            /// C `ldexp`
            #[doc(alias = "ldexp")]
            pub fn scale2(ctx: &mut Context, x: DecimalXX, n: i32) -> DecimalXX {
                let inner = unsafe {
                    __bidXX_ldexp(x.inner, n, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                };

                DecimalXX { inner }
            }

            /// C `lgamma`
            pub [dec_to_dec_round] fn lgamma(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                lgamma
            }

            /// C `nextafter`
            pub [dec_to_dec] fn next_after(ctx: &mut Context, x: DecimalXX, y: DecimalXX) -> DecimalXX {
                nextafter
            }

            /// C `tgamma`
            pub [dec_to_dec_round] fn tgamma(ctx: &mut Context, x: DecimalXX) -> DecimalXX {
                tgamma
            }

            // FIXME more C methods
            // http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1241.pdf
            // http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2341.pdf
        }
    }

    macro_rules! op_letters {
        ($i:ident, 32, 32 -> 32) => {
            paste! { [<__bid32_$i>] }
        };

        ($i:ident, 32, 32, 32 -> 32) => {
            paste! { [<__bid32_$i>] }
        };

        ($i:ident, 64, 64 -> 64) => {
            paste! { [<__bid64_$i>] }
        };
        ($i:ident, 64, 128 -> 64) => {
            paste! { [<__bid64dq_$i>] }
        };
        ($i:ident, 128, 64 -> 64) => {
            paste! { [<__bid64qd_$i>] }
        };
        ($i:ident, 128, 128 -> 64) => {
            paste! { [<__bid64qq_$i>] }
        };

        ($i:ident, 64, 64, 64 -> 64) => {
            paste! { [<__bid64_$i>] }
        };
        ($i:ident, 64, 64, 128 -> 64) => {
            paste! { [<__bid64ddq_$i>] }
        };
        ($i:ident, 64, 128, 64 -> 64) => {
            paste! { [<__bid64dqd_$i>] }
        };
        ($i:ident, 64, 128, 128 -> 64) => {
            paste! { [<__bid64dqq_$i>] }
        };
        ($i:ident, 128, 64, 64 -> 64) => {
            paste! { [<__bid64qdd_$i>] }
        };
        ($i:ident, 128, 64, 128 -> 64) => {
            paste! { [<__bid64qdq_$i>] }
        };
        ($i:ident, 128, 128, 64 -> 64) => {
            paste! { [<__bid64qqd_$i>] }
        };
        ($i:ident, 128, 128, 128 -> 64) => {
            paste! { [<__bid64qqq_$i>] }
        };

        ($i:ident, 64, 64 -> 128) => {
            paste! { [<__bid128dd_$i>] }
        };
        ($i:ident, 64, 128 -> 128) => {
            paste! { [<__bid128dq_$i>] }
        };
        ($i:ident, 128, 64 -> 128) => {
            paste! { [<__bid128qd_$i>] }
        };
        ($i:ident, 128, 128 -> 128) => {
            paste! { [<__bid128_$i>] }
        };

        ($i:ident, 64, 64, 64 -> 128) => {
            paste! { [<__bid128ddd_$i>] }
        };
        ($i:ident, 64, 64, 128 -> 128) => {
            paste! { [<__bid128ddq_$i>] }
        };
        ($i:ident, 64, 128, 64 -> 128) => {
            paste! { [<__bid128dqd_$i>] }
        };
        ($i:ident, 64, 128, 128 -> 128) => {
            paste! { [<__bid128dqq_$i>] }
        };

        ($i:ident, 128, 64, 64 -> 128) => {
            paste! { [<__bid128qdd_$i>] }
        };
        ($i:ident, 128, 64, 128 -> 128) => {
            paste! { [<__bid128qdq_$i>] }
        };
        ($i:ident, 128, 128, 64 -> 128) => {
            paste! { [<__bid128qqd_$i>] }
        };
        ($i:ident, 128, 128, 128 -> 128) => {
            paste! { [<__bid128_$i>] }
        };
    }

    macro_rules! ctx_binop {
        (
            impl DecimalBinop where XX = <$(($l:literal, $r:literal, $ret:literal)),+> $tt:tt
        ) => {
            ctx_binop_def!(impl DecimalBinop $tt);

            $(ctx_binop_impl!(impl DecimalBinop<$l, $r> for $ret $tt);)+
        };
    }

    macro_rules! ctx_binop_def {
        (impl DecimalBinop { $(
            $(#[$attr:meta])*
            pub fn $fn_name:ident;
        )*}) => {

            /// Implemented for pairs of decimal types that can be combined in binary operations.
            pub trait DecimalBinop<L: Decimal, R: Decimal>: Decimal { $(
                #[doc(hidden)]
                fn $fn_name(ctx: &mut Context, x: L, y: R) -> Self;
            )*}

            #[allow(clippy::wrong_self_convention)]
            impl Context { $(
                $(#[$attr])*
                pub fn $fn_name<L: Decimal, R: Decimal, Ret: DecimalBinop<L, R>>(&mut self, x: L, y: R) -> Ret {
                    <Ret as DecimalBinop<L, R>>::$fn_name(self, x, y)
                }
            )*}
        };
    }

    macro_rules! ctx_binop_impl {
        (impl DecimalBinop<$l:literal, $r:literal> for $out:literal {$(
            $(#[$attr:meta])*
            pub fn $fn_name:ident;
        )*}) => { paste! {

            impl DecimalBinop<[<Decimal$l>], [<Decimal$r>]> for [<Decimal$out>] { $(
                $(#[$attr])*
                #[inline]
                fn $fn_name(ctx: &mut Context, x: [<Decimal$l>], y: [<Decimal$r>]) -> [<Decimal$out>] {
                    let inner = unsafe {
                        op_letters!($fn_name, $l, $r -> $out)(x.inner, y.inner, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                    };

                    [<Decimal$out>] { inner }
                }
            )*}
        }};
    }

    ctx_binop! {
        impl DecimalBinop where XX = <
            (32, 32, 32),
            (64, 64, 64),
            (64, 128, 64),
            (128, 64, 64),
            (128, 128, 64),
            (64, 64, 128),
            (64, 128, 128),
            (128, 64, 128),
            (128, 128, 128)
        > {
            /// IEEE 754 5.4.1 **addition**
            #[doc(alias = "addition")]
            pub fn add;

            /// IEEE 754 5.4.1 **subtraction**
            #[doc(alias = "subtraction")]
            pub fn sub;

            /// IEEE 754 5.4.1 **multiplication**
            #[doc(alias = "multiplication")]
            pub fn mul;

            /// IEEE 754 5.4.1 **division**
            #[doc(alias = "division")]
            pub fn div;
        }
    }

    macro_rules! ctx_ternop {
        (
            impl DecimalTernop where XX = <$(($l:literal, $c:literal, $r:literal, $ret:literal)),+> $tt:tt
        ) => {
            ctx_ternop_def!(impl DecimalTernop $tt);

            $(ctx_ternop_impl!(impl DecimalTernop<$l, $c, $r> for $ret $tt);)+
        };
    }

    macro_rules! ctx_ternop_def {
        (impl DecimalTernop { $(
            $(#[$attr:meta])*
            pub fn $fn_name:ident { $inner:ident };
        )*}) => {

            /// Implemented for groups of decimal types that can be combined in ternary operations.
            pub trait DecimalTernop<L: Decimal, C: Decimal, R: Decimal>: Decimal { $(
                #[doc(hidden)]
                fn $fn_name(ctx: &mut Context, x: L, y: C, z: R) -> Self;
            )*}

            #[allow(clippy::wrong_self_convention)]
            impl Context { $(
                $(#[$attr])*
                pub fn $fn_name<L: Decimal, C: Decimal, R: Decimal, Ret: DecimalTernop<L, C, R>>(&mut self, x: L, y: C, z: R) -> Ret {
                    <Ret as DecimalTernop<L, C, R>>::$fn_name(self, x, y, z)
                }
            )*}
        };
    }

    macro_rules! ctx_ternop_impl {
        (impl DecimalTernop<$l:literal, $c:literal, $r:literal> for $out:literal {$(
            $(#[$attr:meta])*
            pub fn $fn_name:ident  { $inner:ident };
        )*}) => { paste! {

            impl DecimalTernop<[<Decimal$l>], [<Decimal$c>], [<Decimal$r>]> for [<Decimal$out>] { $(
                $(#[$attr])*
                #[inline]
                fn $fn_name(ctx: &mut Context, x: [<Decimal$l>], y: [<Decimal$c>], z: [<Decimal$r>]) -> [<Decimal$out>] {
                    let inner = unsafe {
                        op_letters!($inner, $l, $c, $r -> $out)(x.inner, y.inner, z.inner, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                    };

                    [<Decimal$out>] { inner }
                }
            )*}
        }};
    }

    ctx_ternop! {
        impl DecimalTernop where XX = <
            (32, 32, 32, 32),

            (64, 64, 64, 64),
            (64, 128, 64, 64),
            (128, 64, 64, 64),
            (128, 128, 64, 64),
            (64, 64, 128, 64),
            (64, 128, 128, 64),
            (128, 64, 128, 64),
            (128, 128, 128, 64),

            (64, 64, 64, 128),
            (64, 128, 64, 128),
            (128, 64, 64, 128),
            (128, 128, 64, 128),
            (64, 64, 128, 128),
            (64, 128, 128, 128),
            (128, 64, 128, 128),
            (128, 128, 128, 128)
        > {
            /// IEEE 754 5.4.1 **fusedMultiplyAdd**
            #[doc(alias = "fusedMultiplyAdd")]
            pub fn mul_add { fma };
        }
    }
}

use context::{Context, Decimal, Flags};

macro_rules! only_32 {
    (32, $($tt:tt)*) => { $($tt)* };
    (64, $($tt:tt)*) => { };
    (128, $($tt:tt)*) => {  };
}

macro_rules! only_32_64 {
    (32, $($tt:tt)*) => {  $($tt)* };
    (64, $($tt:tt)*) => { $($tt)* };
    (128, $($tt:tt)*) => { };
}

#[cfg(feature = "funty")]
macro_rules! only_64 {
    (32, $($tt:tt)*) => { };
    (64, $($tt:tt)*) => { $($tt)* };
    (128, $($tt:tt)*) => {  };
}

macro_rules! only_64_128 {
    (32, $($tt:tt)*) => { };
    (64, $($tt:tt)*) => { $($tt)* };
    (128, $($tt:tt)*) => { $($tt)* };
}

macro_rules! only_128 {
    (32, $($tt:tt)*) => { };
    (64, $($tt:tt)*) => { };
    (128, $($tt:tt)*) => { $($tt)* };
}

macro_rules! decimal_op_simple_bool {
    ($x:literal, $(#[$attr:meta])* pub fn $fn:ident $(($($arg:ident),+))? { $c_fn:ident }) => {
        paste! {
            $(#[$attr])*
            #[inline]
            pub fn $fn(self $($(, $arg: Self)+)?) -> bool {
                (unsafe { [<__bid $x _ $c_fn>](self.inner $($(, $arg.inner)+)?) }) != 0
            }
        }
    };
}

macro_rules! decimal_binop_trait {
    (impl $trait:ident, $fn:ident $(, $assign_trait:ident)? for $x:literal) => {
        paste! {
            impl $trait for [<Decimal$x>] {
                type Output = Self;

                #[inline]
                fn $fn(self, rhs: Self) -> Self::Output {
                    Context::new().$fn(self, rhs)
                }
            }

            forward_ref_binop!(impl $trait, $fn for [<Decimal$x>], [<Decimal$x>]);

            $(
                impl $assign_trait for [<Decimal$x>] {

                    #[inline]
                    fn [<$fn _assign>](&mut self, rhs: Self) {
                        *self = (*self).$fn(rhs);
                    }
                }

                forward_ref_op_assign!(impl $assign_trait, [<$fn _assign>] for [<Decimal$x>], [<Decimal$x>]);
            )?
        }
    };
}

macro_rules! decimal_op_forward {
    (
        $(#[$attr:meta])*
        pub fn $fn:ident($($arg:ident $(: $arg_ty:ty)?),*)  -> $return_ty:ty
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $fn($($arg $(: $arg_ty)?),*) -> $return_ty {
            Context::new().$fn($($arg),*)
        }

    };
}

macro_rules! per_width {
    (32, $l32:expr, $l64:expr, $l128:expr) => {
        $l32
    };
    (64, $l32:expr, $l64:expr, $l128:expr) => {
        $l64
    };
    (128, $l32:expr, $l64:expr, $l128:expr) => {
        $l128
    };
}

macro_rules! decimal_from_int_impl {
    ($x: literal, $($(#[$attr:meta])* $int:ty),*) => {
        paste! { $(
            $(#[$attr])*
            impl From<$int> for [<Decimal$x>] {
                #[inline]
                fn from(small: $int) -> Self {
                    let mut ctx = Context::new();
                    let result = ctx.from_int(small);
                    debug_assert!(!ctx.flags.contains(Flags::INEXACT));
                    result
                }
            }
        )*}
    };
}

macro_rules! from_convert_format_impl {
    ($dest:ty, $src:ty) => {
        impl From<$src> for $dest {
            #[inline]
            fn from(src: $src) -> Self {
                let mut ctx = Context::new();
                let result = ctx.convert_format(src);
                debug_assert!(!ctx.flags.contains(Flags::INEXACT));
                result
            }
        }
    };
}

#[cfg(feature = "cast")]
macro_rules! impl_cast_no_overflow {
    ($src:ty, $dst:ty) => {
        impl cast::From<$src> for $dst {
            type Output = Self;

            #[inline]
            fn cast(src: $src) -> Self::Output {
                let mut ctx = Context::new();
                let result =
                    <$dst as convert::DecimalConvertFormat<$src>>::convert_format(&mut ctx, src);
                debug_assert!(result.is_finite());
                result
            }
        }
    };
}

#[cfg(feature = "cast")]
macro_rules! impl_cast_overflow {
    ($src:ty, $dst:ty) => {
        impl cast::From<$src> for $dst {
            type Output = Result<Self, cast::Error>;

            #[inline]
            fn cast(src: $src) -> Self::Output {
                let mut ctx = Context::new();
                let result =
                    <$dst as convert::DecimalConvertFormat<$src>>::convert_format(&mut ctx, src);

                if ctx.flags.contains(Flags::OVERFLOW) {
                    if src.is_sign_positive() {
                        Err(cast::Error::Overflow)
                    } else {
                        Err(cast::Error::Underflow)
                    }
                } else {
                    Ok(result)
                }
            }
        }
    };
}

macro_rules! convert_format_impl_forward {
    ($x:literal, [$($ty:ty),*]) => {
        convert_format_impl_forward!($x -> [$($ty),*]);
        convert_format_impl_forward!($x <- [$($ty),*]);
    };
    ($x:literal -> [$($ty:ty),*]) => {
        paste! { $(
            #[cfg(feature = "alga")]
            impl alga::general::SubsetOf<$ty> for [<Decimal$x>] {
                #[inline]
                fn to_superset(&self) -> $ty {
                    <Self as num_traits::AsPrimitive<$ty>>::as_(*self)
                }

                #[inline]
                unsafe fn from_superset_unchecked(element: &$ty) -> Self {
                    <$ty as num_traits::AsPrimitive<Self>>::as_(*element)
                }

                #[inline]
                fn is_in_subset(_: &$ty) -> bool {
                    true
                }
            }

            #[cfg(feature = "az")]
            impl az::Cast<$ty> for [<Decimal$x>] {
                #[inline]
                fn cast(self) -> $ty {
                    self.convert_into()
                }
            }

            #[cfg(feature = "az")]
            impl az::CheckedCast<$ty> for [<Decimal$x>] {
                #[inline]
                fn checked_cast(self) -> Option<$ty> {
                    Some(az::cast(self))
                }
            }

            #[cfg(feature = "az")]
            impl az::UnwrappedCast<$ty> for [<Decimal$x>] {
                #[inline]
                fn unwrapped_cast(self) -> $ty {
                    az::cast(self)
                }
            }
            #[cfg(feature = "num-traits")]
            impl num_traits::AsPrimitive<$ty> for [<Decimal$x>] {
                #[inline]
                fn as_(self) -> $ty {
                    self.convert_into()
                }
            }

            #[cfg(feature = "simba")]
            impl simba::scalar::SubsetOf<$ty> for [<Decimal$x>] {
                #[inline]
                fn to_superset(&self) -> $ty {
                    <Self as num_traits::AsPrimitive<$ty>>::as_(*self)
                }

                #[inline]
                fn from_superset_unchecked(element: &$ty) -> Self {
                    <$ty as num_traits::AsPrimitive<Self>>::as_(*element)
                }

                #[inline]
                fn is_in_subset(_: &$ty) -> bool {
                    true
                }
            }
        )* }
    };
    ($x:literal <- [$($ty:ty),*]) => {
        paste! { $(
            #[cfg(feature = "alga")]
            impl alga::general::SubsetOf<[<Decimal$x>]> for $ty {
                #[inline]
                fn to_superset(&self) -> [<Decimal$x>] {
                    <Self as num_traits::AsPrimitive<[<Decimal$x>]>>::as_(*self)
                }

                #[inline]
                unsafe fn from_superset_unchecked(element: &[<Decimal$x>]) -> Self {
                    <[<Decimal$x>] as num_traits::AsPrimitive<Self>>::as_(*element)
                }

                #[inline]
                fn is_in_subset(_: &[<Decimal$x>]) -> bool {
                    true
                }
            }

            #[cfg(feature = "simba")]
            impl simba::scalar::SubsetOf<[<Decimal$x>]> for $ty {
                #[inline]
                fn to_superset(&self) -> [<Decimal$x>] {
                    <Self as num_traits::AsPrimitive<[<Decimal$x>]>>::as_(*self)
                }

                #[inline]
                fn from_superset_unchecked(element: &[<Decimal$x>]) -> Self {
                    <[<Decimal$x>] as num_traits::AsPrimitive<Self>>::as_(*element)
                }

                #[inline]
                fn is_in_subset(_: &[<Decimal$x>]) -> bool {
                    true
                }
            }
        )* }

        convert_format_impl_forward!($x <- nosubset [$($ty),*]);
    };
    ($x:literal <- nosubset [$($ty:ty),*]) => {
        paste! { $(
            #[cfg(feature = "az")]
            impl az::Cast<[<Decimal$x>]> for $ty {
                #[inline]
                fn cast(self) -> [<Decimal$x>] {
                    [<Decimal$x>]::convert_from(self)
                }
            }

            #[cfg(feature = "az")]
            impl az::CheckedCast<[<Decimal$x>]> for $ty {
                #[inline]
                fn checked_cast(self) -> Option<[<Decimal$x>]> {
                    Some(az::cast(self))
                }
            }

            #[cfg(feature = "az")]
            impl az::UnwrappedCast<[<Decimal$x>]> for $ty {
                #[inline]
                fn unwrapped_cast(self) -> [<Decimal$x>] {
                    az::cast(self)
                }
            }

            #[cfg(feature = "num-traits")]
            impl num_traits::AsPrimitive<[<Decimal$x>]> for $ty {
                #[inline]
                fn as_(self) -> [<Decimal$x>] {
                    [<Decimal$x>]::convert_from(self)
                }
            }
        )* }
    };
}

#[cfg(any(feature = "alga", feature = "approx"))]
macro_rules! approx_impl {
    ($x: literal, $approx:ident) => {
        paste! {
            impl $approx::AbsDiffEq<Self> for [<Decimal$x>] {
                type Epsilon = Self;

                #[inline]
                fn default_epsilon() -> Self {
                    [<Decimal$x>]::EPSILON
                }

                #[inline]
                fn abs_diff_eq(&self, other: &Self, epsilon: Self) -> bool {
                    (self - other).abs() <= epsilon
                }
            }

            impl $approx::RelativeEq for [<Decimal$x>] {
                #[inline]
                fn default_max_relative() -> Self {
                    [<Decimal$x>]::EPSILON
                }

                #[inline]
                fn relative_eq(&self, other: &Self, epsilon: Self, max_relative: Self) -> bool {
                    // Handle same infinities
                    if self == other {
                        return true;
                    }

                    // Handle remaining infinities
                    if self.is_infinite() || other.is_infinite() {
                        return false;
                    }

                    let abs_diff = (self - other).abs();

                    // For when the numbers are really close together
                    if abs_diff <= epsilon {
                        return true;
                    }

                    let abs_self = self.abs();
                    let abs_other = other.abs();

                    let largest = if abs_other > abs_self {
                        abs_other
                    } else {
                        abs_self
                    };

                    // Use a relative difference comparison
                    abs_diff <= largest * max_relative
                }
            }

            impl $approx::UlpsEq for [<Decimal$x>] {
                #[inline]
                fn default_max_ulps() -> u32 {
                    4
                }

                /// FIXME find more accurate algorithm that's not O(n). Also update `float_eq`
                #[inline]
                fn ulps_eq(&self, other: &Self, epsilon: Self, max_ulps: u32) -> bool {
                    // For when the numbers are really close together
                    if <Self as $approx::AbsDiffEq<Self>>::abs_diff_eq(self, other, epsilon) {
                        return true;
                    }

                    let (l, r) = (*self, *other);

                    // Trivial negative sign check
                    let (self_abs, other_abs) = match (l.is_sign_positive(), r.is_sign_positive()) {
                        (true, true) => (l, r),
                        (false, false) => (-l, -r),
                        _ => return false,
                    };

                    // ULPS difference comparison
                    let diff = self_abs - other_abs;
                    let (abs_diff, max);
                    if diff.is_sign_positive() {
                        (abs_diff, max) = (diff, self_abs);
                    } else {
                        (abs_diff, max) = (-diff, other_abs);
                    }

                    let one_ulp = max - Context::new().next_down(max);

                    let max_ulps: Self = [<Decimal$x>]::from_int(max_ulps);

                    abs_diff <= (max_ulps * one_ulp)
                }
            }
        }
    };
}

#[cfg(any(feature = "funty", feature = "num-traits"))]
macro_rules! as_to_int_fn {
    ($($dst:ident),*) => {$(
        paste! {
            #[inline]
            fn [<as_$dst>](self) -> $dst {
                self.to_int()
            }
        }
    )*};
}

/// Error returned by `from_str_radix` when a radix other than 10 is used.
#[cfg(feature = "num-traits")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnsupportedRadixError;

#[cfg(feature = "num-traits")]
impl fmt::Display for UnsupportedRadixError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Only radix 10 is supported")
    }
}

#[cfg(feature = "num-traits")]
macro_rules! from_primitive_int {
    ($x:literal, [$($src:ident),*]) => {
        paste! { $(
            #[inline]
            fn [<from_$src>](n: $src) -> Option<Self> {
                Some([<Decimal$x>]::from_int(n))
            }
        )* }
    };
}

#[cfg(feature = "num-traits")]
macro_rules! from_primitive_float {
    ($x:literal,[$($src:ident),*]) => {
        paste! { $(
            #[inline]
            fn [<from_$src>](n: $src) -> Option<Self> {
                Some([<Decimal$x>]::convert_from(n))
            }
        )* }
    };
}

#[cfg(feature = "num-traits")]
macro_rules! to_primitive_to_int_fn {
    ($($dst:ident),*) => {$(
        paste! {
            #[inline]
            fn [<to_$dst>](&self) -> Option<$dst> {
                self.to_int_checked()
            }
        }
    )*};
}

#[cfg(feature = "num-traits")]
macro_rules! trait_forward {
    ($x:expr, $(#[$attr:meta])* $fn:ident($($param:ident $(: $param_ty:ty)?),*) -> $return:ty) => {
        paste! {
            $(#[$attr])*
            #[inline]
            fn $fn($($param $(: $param_ty)?),*) -> $return {
                [<Decimal$x>]::$fn($($param),*)
            }
        }
    }
}

#[cfg(feature = "num-traits")]
macro_rules! trait_forward_const {
    ($x:expr, $(#[$attr:meta])* $fn:ident() -> $return:ty { $const:ident }) => {
        paste! {
            $(#[$attr])*
            #[inline]
            fn $fn() -> $return {
                [<Decimal$x>]::$const
            }
        }
    }
}

#[cfg(feature = "num-traits")]
macro_rules! trait_forward_const_math {
    ($x:literal, $(#[$attr:meta])* $fn:ident { $const:ident }) => {
        paste! {
            $(#[$attr])*
            #[inline]
            fn $fn() -> Self {
                [<decimal$x>]::consts::$const
            }
        }
    };

    ($x:literal, $(#[$attr:meta])* $fn:ident) => {
        trait_forward_const_math!($x, $(#[$attr])* $fn { $fn });
    };
}

#[cfg(feature = "rug")]
macro_rules! rug_assign_from {
    ($T:ty; $op:ident; $Imp:ident $method:ident) => {
        impl $Imp for $T {
            #[inline]
            fn $method(&mut self, lhs: $T) {
                *self = lhs.$op(*self);
            }
        }
        impl $Imp<&$T> for $T {
            #[inline]
            fn $method(&mut self, lhs: &$T) {
                *self = (*lhs).$op(*self);
            }
        }
    };
}

#[cfg(feature = "half")]
impl private::Sealed for half::bf16 {}
#[cfg(feature = "half")]
impl private::Sealed for half::f16 {}
impl private::Sealed for f32 {}
impl private::Sealed for f64 {}

#[allow(clippy::wrong_self_convention)]
impl Context {
    /// IEEE 754 5.4.1 **convertFromInt**
    #[doc(alias = "convertFromInt")]
    #[inline]
    pub fn from_int<Int, Dest>(&mut self, int: Int) -> Dest
    where
        Dest: convert::DecimalFromInt<Int>,
        Int: private::Sealed,
    {
        <Dest as convert::DecimalFromInt<Int>>::from_int(self, int)
    }

    /// IEEE 754 5.4.2 **convertFormat**
    #[doc(alias = "convertFormat")]
    #[inline]
    pub fn convert_format<Src, Dest>(&mut self, src: Src) -> Dest
    where
        Dest: convert::DecimalConvertFormat<Src>,
        Src: private::Sealed,
    {
        <Dest as convert::DecimalConvertFormat<Src>>::convert_format(self, src)
    }
}

macro_rules! conversion_traits {
    (($($x:literal),*), $roundings:tt, $types_small:tt, $types_32:tt, $types_64:tt, $equiv_types:tt, $ubig_types:tt, $ibig_types:tt) => {
        conversion_traits_def!($roundings);
        $(
            decimal_to_int_impl!($x, $roundings, $types_small);
            decimal_to_int_impl!($x, $roundings, $types_32);
            decimal_to_int_impl!($x, $roundings, $types_64);
            decimal_from_int_impl_small!($x, $types_small);
            decimal_from_int_impl_32!($x, $types_32);
            decimal_from_int_impl_64!($x, $types_64);
            conversion_traits_impl_equiv!($x, $roundings, $equiv_types);
            conversion_traits_impl_ubig!($x, $roundings, $ubig_types);
            conversion_traits_impl_ibig!($x, $roundings, $ibig_types);
        )*

        impl_sealed!($types_small, $types_32, $types_64, $equiv_types, $ubig_types, $ibig_types);
    };
}

macro_rules! impl_sealed {
    ($([$( $(#[$attr:meta])*  ($type:ty $(, $tt:tt)*)),*]),*) => {
        $($($(#[$attr])* impl private::Sealed for $type {})*)*
    };
}

macro_rules! conversion_traits_def {
    ([$(($rust_round:ident, $ieee_round:ident, $c_round:ident)),*]) => {
        paste! {
            pub mod convert {
                //! Traits for converting between decimals and integers.

                use crate::*;

                /// Implemented for decimals that can be converted to the specified integer.
                pub trait DecimalToInt<Int: private::Sealed>: Decimal + Sized {
                    $(
                        #[doc(hidden)]
                        fn [<to_int_ $rust_round>](ctx: &mut Context, n: Self) -> Int;

                        #[doc(hidden)]
                        fn [<to_int_exact_ $rust_round>](ctx: &mut Context, n: Self) -> Int;
                    )*

                    #[doc(hidden)]
                    const INT_MIN: Int;

                    #[doc(hidden)]
                    const INT_MAX: Int;

                    #[doc(hidden)]
                    const INT_ZERO: Int;
                }

                /// Implemented for decimals that can be converted from other decimals of different size.
                pub trait DecimalConvertFormat<Src: private::Sealed>: private::Sealed + Sized {
                    #[doc(hidden)]
                    fn convert_format(ctx: &mut Context, src: Src) -> Self;
                }

                /// Implemented for decimals that can be converted from integers.
                pub trait DecimalFromInt<Int: private::Sealed>: Decimal + Sized {
                    #[doc(hidden)]
                    fn from_int(ctx: &mut Context, i: Int) -> Self;
                }
            }

            #[allow(clippy::wrong_self_convention)]
            impl Context {
                $(
                    #[doc = "IEEE 754 5.4.1 **convertToInteger" $ieee_round "**"]
                    #[doc(alias = "convertToInteger" $ieee_round)]
                    #[inline]
                    pub fn [<to_int_$rust_round>]<Dec, Int>(&mut self, x: Dec) -> Int
                    where
                        Dec: convert::DecimalToInt<Int>,
                        Int: private::Sealed,
                    {
                        <Dec as convert::DecimalToInt<Int>>::[<to_int_$rust_round>](self, x)
                    }

                    #[doc = "IEEE 754 5.4.1 **convertToIntegerExact" $ieee_round "**"]
                    #[doc(alias = "convertToIntegerExact" $ieee_round)]
                    #[inline]
                    pub fn [<to_int_exact_$rust_round>]<Dec, Int>(&mut self, x: Dec) -> Int
                    where
                        Dec: convert::DecimalToInt<Int>,
                        Int: private::Sealed,
                    {
                        <Dec as convert::DecimalToInt<Int>>::[<to_int_exact_$rust_round>](self, x)
                    }
                )*
            }
        }
    };
}

macro_rules! decimal_to_int_impl {
    (
        $x:literal,
        $roundings:tt,
        [$(($rust_int:ident, $c_int:ident $(, $bigger:ident)?)),*]
    ) => {
        $(decimal_to_int_impl!($x, $roundings, ($rust_int, $c_int));)*
    };
    (
        $x:literal,
        [$(($rust_round:ident, $ieee_round:ident, $c_round:ident)),*],
        ($rust_int:ident, $c_int:ident)
    ) => {
        paste! {
            impl convert::DecimalToInt<$rust_int> for [<Decimal$x>] {
                $(
                    #[doc(hidden)]
                    #[inline]
                    fn [<to_int_ $rust_round>](ctx: &mut Context, x: Self) -> $rust_int {
                        unsafe { [<__bid $x _to_ $c_int _ $c_round>](x.inner, ctx.flags.as_mut_ptr()) }
                    }

                    #[doc(hidden)]
                    #[inline]
                    fn [<to_int_exact_ $rust_round>](ctx: &mut Context, x: Self) -> $rust_int {
                        unsafe { [<__bid $x _to_ $c_int _x $c_round>](x.inner, ctx.flags.as_mut_ptr()) }
                    }
                )*

                #[doc(hidden)]
                const INT_MIN: $rust_int = $rust_int::MIN;

                #[doc(hidden)]
                const INT_MAX: $rust_int = $rust_int::MAX;

                #[doc(hidden)]
                const INT_ZERO: $rust_int = 0;
            }
        }

        conversion_traits_forward!($x, $rust_int);
    };
}

macro_rules! decimal_from_int_impl_small {
    ($x:literal, [$(($rust_int:ident, $c_int:ident, $bigger:ident)),*]) => {$(
        paste! {
            impl convert::DecimalFromInt<$rust_int> for [<Decimal$x>] {
                #[doc(hidden)]
                #[inline]
                fn from_int(ctx: &mut Context, int: $rust_int) -> Self {
                    convert::DecimalFromInt::<$bigger>::from_int(ctx, int.into())
                }
            }
        }
    )*};
}

macro_rules! decimal_from_int_impl_32 {
    ($x:literal, [$(($rust_int:ident, $c_int:ident)),*]) => {$(
        paste! {
            only_32!($x,
                impl convert::DecimalFromInt<$rust_int> for [<Decimal$x>] {
                    #[doc(hidden)]
                    #[inline]
                    fn from_int(ctx: &mut Context, int: $rust_int) -> Self {
                        let inner = unsafe {
                            [<__bid $x _from_ $c_int>](int, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                        };

                        [<Decimal$x>] { inner }
                    }
                }
            );

            only_64_128!($x,
                impl convert::DecimalFromInt<$rust_int> for [<Decimal$x>] {
                    #[doc(hidden)]
                    #[inline]
                    fn from_int(_: &mut Context, int: $rust_int) -> Self {
                        let inner = unsafe {
                            [<__bid $x _from_ $c_int>](int)
                        };

                        [<Decimal$x>] { inner }
                    }
                }
            );
        }
    )*};
}

macro_rules! decimal_from_int_impl_64 {
    ($x:literal, [$(($rust_int:ident, $c_int:ident)),*]) => {$(
        paste! {
            only_32_64!($x,
                impl convert::DecimalFromInt<$rust_int> for [<Decimal$x>] {
                    #[doc(hidden)]
                    #[inline]
                    fn from_int(ctx: &mut Context, int: $rust_int) -> Self {
                        let inner = unsafe {
                            [<__bid $x _from_ $c_int>](int, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                        };

                        [<Decimal$x>] { inner }
                    }
                }
            );

            only_128!($x,
                impl convert::DecimalFromInt<$rust_int> for [<Decimal$x>] {
                    #[doc(hidden)]
                    #[inline]
                    fn from_int(_: &mut Context, int: $rust_int) -> Self {
                        let inner = unsafe {
                            [<__bid $x _from_ $c_int>](int)
                        };

                        [<Decimal$x>] { inner }
                    }
                }
            );
        }
    )*};
}

macro_rules! conversion_traits_impl_equiv {
    (
        $x:literal,
        $roundings:tt,
        [$(($size:ident, $equiv:ident)),*]
    ) => {
        $(conversion_traits_impl_equiv!($x, $roundings, ($size, $equiv));)*
    };
    (
        $x:literal,
        [$(($rust_round:ident, $ieee_round:ident, $c_round:ident)),*],
        ($size:ident, $equiv:ident)
    ) => {
        paste! {
            impl convert::DecimalToInt<$size> for [<Decimal$x>] {
                $(
                    #[doc(hidden)]
                    #[inline]
                    fn [<to_int_ $rust_round>](ctx: &mut Context, x: Self) -> $size {
                        <[<Decimal$x>] as convert::DecimalToInt<$equiv>>::[<to_int_ $rust_round>](ctx, x) as $size
                    }

                    #[doc(hidden)]
                    #[inline]
                    fn [<to_int_exact_ $rust_round>](ctx: &mut Context, x: Self) -> $size {
                        <[<Decimal$x>] as convert::DecimalToInt<$equiv>>::[<to_int_exact_ $rust_round>](ctx, x) as $size
                    }
                )*

                #[doc(hidden)]
                const INT_MIN: $size = $size::MIN;

                #[doc(hidden)]
                const INT_MAX: $size = $size::MAX;

                #[doc(hidden)]
                const INT_ZERO: $size = 0;
            }

            impl convert::DecimalFromInt<$size> for [<Decimal$x>] {
                #[doc(hidden)]
                #[inline]
                fn from_int(ctx: &mut Context, int: $size) -> Self {
                    convert::DecimalFromInt::<$equiv>::from_int(ctx, int as $equiv)
                }
            }
        }

        conversion_traits_forward!($x, $size);
    };
}

macro_rules! conversion_traits_impl_ubig {
    (
        $x:literal,
        $roundings:tt,
        [$($(#[$attr:meta])* ($bigint:ty, ($min:expr, $zero:expr))),*]
    ) => { $(conversion_traits_impl_ubig!($x, $roundings, $(#[$attr])* ($bigint, ($min, $zero)));)* };
    (
        $x:literal,
        [$(($rust_round:ident, $ieee_round:ident, $c_round:ident)),*],
        $(#[$attr:meta])* ($bigint:ty, ($min:expr, $zero:expr))
    ) => {
        paste! {
            $(#[$attr])*
            impl convert::DecimalToInt<$bigint> for [<Decimal$x>] {
                $(
                    #[doc(hidden)]
                    #[inline]
                    fn [<to_int_ $rust_round>](ctx: &mut Context, x: Self) -> $bigint {
                        let rounded = ctx.$rust_round(x);

                        let (significand, exponent, signed) = rounded.integer_decode();
                        if signed {
                            if significand != 0 {
                                ctx.flags = ctx.flags.union(Flags::INVALID_OPERATION)
                            }
                            return 0u128.into();
                        }

                        debug_assert!(exponent >= 0 || !x.is_finite());

                        let result = $bigint::from(10_u128)
                            .checked_pow((exponent as u32).into())
                            .and_then(|e| $bigint::from(significand as u128).checked_mul(e));
                        match result {
                            Some(i) => i,
                            None => {
                                ctx.flags = ctx.flags.union(Flags::INVALID_OPERATION);
                                $bigint::MAX
                            }
                        }
                    }

                    #[doc(hidden)]
                    #[inline]
                    fn [<to_int_exact_ $rust_round>](ctx: &mut Context, x: Self) -> $bigint {
                        let orig_rounding = ctx.get_rounding();
                        ctx.set_rounding(Rounding::$ieee_round);
                        let rounded = ctx.round_to_integral_exact(x);
                        ctx.set_rounding(orig_rounding);

                        let (significand, exponent, signed) = rounded.integer_decode();
                        if signed {
                            if significand != 0 {
                                ctx.flags = ctx.flags.union(Flags::INVALID_OPERATION)
                            }
                            return 0u128.into();
                        }

                        debug_assert!(exponent >= 0 || !x.is_finite());

                        let result = $bigint::from(10_u128)
                            .checked_pow((exponent as u32).into())
                            .and_then(|e| $bigint::from(significand as u128).checked_mul(e));
                        match result {
                            Some(i) => i,
                            None => {
                                ctx.flags = ctx.flags.union(Flags::INVALID_OPERATION);
                                $bigint::MAX
                            }
                        }
                    }
                )*

                #[doc(hidden)]
                const INT_MIN: $bigint = $min;

                #[doc(hidden)]
                const INT_MAX: $bigint = $bigint::MAX;

                #[doc(hidden)]
                const INT_ZERO: $bigint = $zero;
            }

            $(#[$attr])*
            impl convert::DecimalFromInt<$bigint> for [<Decimal$x>] {
                #[doc(hidden)]
                #[inline]
                fn from_int(ctx: &mut Context, int: $bigint) -> Self {
                    Context::from_c_str(
                        ctx,
                        // SAFETY: string representation of an int won't have a null byte
                        &(unsafe { CString::new(int.to_string()).unwrap_unchecked() })
                    )
                }
            }
        }

        $(#[$attr])*
        conversion_traits_forward!($x, $bigint, $min);
    };
}

macro_rules! conversion_traits_impl_ibig {
    (
        $x:literal,
        $roundings:tt,
        [$($(#[$attr:meta])* ($bigint:ty, ($min:expr, $zero:expr))),*]
    ) => { $(conversion_traits_impl_ibig!($x, $roundings, $(#[$attr])* ($bigint, ($min, $zero)));)* };
    (
        $x:literal,
        [$(($rust_round:ident, $ieee_round:ident, $c_round:ident)),*],
        $(#[$attr:meta])* ($bigint:ty, ($min:expr, $zero:expr))
    ) => {
        paste! {
            $(#[$attr])*
            impl convert::DecimalToInt<$bigint> for [<Decimal$x>] {
                $(
                    #[doc(hidden)]
                    #[inline]
                    fn [<to_int_ $rust_round>](ctx: &mut Context, x: Self) -> $bigint {
                        let rounded = ctx.$rust_round(x);

                        let (significand, exponent, signed) = rounded.integer_decode();

                        debug_assert!(exponent >= 0 || !x.is_finite());

                        let result = $bigint::from(10_i128)
                            .checked_pow((exponent as u32).into())
                            .and_then(|e| $bigint::from(significand as i128).checked_mul(e))
                            .map(|u| u * (if signed { $bigint::from(-1) } else { $bigint::from(1) }));
                        match result {
                            Some(i) => i,
                            None => {
                                ctx.flags = ctx.flags.union(Flags::INVALID_OPERATION);
                                if signed { $min } else { $bigint::MAX }
                            }
                        }
                    }

                    #[doc(hidden)]
                    #[inline]
                    fn [<to_int_exact_ $rust_round>](ctx: &mut Context, x: Self) -> $bigint {
                        let orig_rounding = ctx.get_rounding();
                        ctx.set_rounding(Rounding::$ieee_round);
                        let rounded = ctx.round_to_integral_exact(x);
                        ctx.set_rounding(orig_rounding);

                        let (significand, exponent, signed) = rounded.integer_decode();

                        debug_assert!(exponent >= 0 || !x.is_finite());

                        let result = $bigint::from(10_i128)
                            .checked_pow((exponent as u32).into())
                            .and_then(|e| $bigint::from(significand as i128).checked_mul(e))
                            .map(|u| u * (if signed { $bigint::from(-1) } else { $bigint::from(1) }));
                        match result {
                            Some(i) => i,
                            None => {
                                ctx.flags = ctx.flags.union(Flags::INVALID_OPERATION);
                                if signed { $min } else { $bigint::MAX }
                            }
                        }
                    }
                )*

                #[doc(hidden)]
                const INT_MIN: $bigint = $min;

                #[doc(hidden)]
                const INT_MAX: $bigint = $bigint::MAX;

                #[doc(hidden)]
                const INT_ZERO: $bigint = $zero;
            }

            $(#[$attr])*
            impl convert::DecimalFromInt<$bigint> for [<Decimal$x>] {
                #[doc(hidden)]
                #[inline]
                fn from_int(ctx: &mut Context, int: $bigint) -> Self {
                    Context::from_c_str(
                        ctx,
                        // SAFETY: string representation of an int won't have a null byte
                        &(unsafe { CString::new(int.to_string()).unwrap_unchecked() })
                    )
                }
            }
        }

        $(#[$attr])*
        conversion_traits_forward!($x, $bigint, $min);
    };
}

#[cfg(feature = "primitive-types")]
macro_rules! if_u512 {
    (primitive_types::U512, { $($if_512:tt)* }, { $($otherwise:tt)* }) => { $($if_512)* };
    ($int_ty:ty, { $($if_512:tt)* }, { $($otherwise:tt)* }) => { $($otherwise)* };
}

macro_rules! conversion_traits_forward {
    ($x:literal, $int:ty) => {
        conversion_traits_forward!($x, $int, (<$int>::MIN));
    };
    ($x:literal, $int:ty, $min_expr:expr) => {
        paste! {

            #[cfg(feature = "alga")]
            impl alga::general::SubsetOf<[<Decimal$x>]> for $int {
                #[inline]
                fn to_superset(&self) -> [<Decimal$x>] {
                    <Self as num_traits::AsPrimitive<[<Decimal$x>]>>::as_(*self)
                }

                #[inline]
                unsafe fn from_superset_unchecked(element: &[<Decimal$x>]) -> Self {
                    <[<Decimal$x>] as num_traits::AsPrimitive<Self>>::as_(*element)
                }

                #[inline]
                fn is_in_subset(_: &[<Decimal$x>]) -> bool {
                    true
                }
            }

            #[cfg(feature = "az")]
            impl az::CheckedCast<$int> for [<Decimal$x>] {
                #[inline]
                fn checked_cast(self) -> Option<$int> {
                    self.to_int_checked()
                }
            }

            #[cfg(feature = "az")]
            impl az::SaturatingCast<$int> for [<Decimal$x>] {
                #[inline]
                fn saturating_cast(self) -> $int {
                    if self.is_nan() {
                        panic!("NaN")
                    }

                    match az::CheckedCast::<$int>::checked_cast(self) {
                        Some(result) => result,
                        None => if self.is_sign_negative() { $min_expr } else { $int::MAX }
                    }
                }
            }

            #[cfg(feature = "az")]
            impl az::UnwrappedCast<$int> for [<Decimal$x>] {
                #[inline]
                fn unwrapped_cast(self) -> $int {
                    az::CheckedCast::checked_cast(self).expect("overflow")
                }
            }

            #[cfg(feature = "az")]
            impl az::Cast<[<Decimal$x>]> for $int {
                #[inline]
                fn cast(self) -> [<Decimal$x>] {
                    [<Decimal$x>]::from_int(self)
                }
            }

            #[cfg(feature = "az")]
            impl az::CheckedCast<[<Decimal$x>]> for $int {
                #[inline]
                fn checked_cast(self) -> Option<[<Decimal$x>]> {
                    Some(az::cast(self))
                }
            }

            #[cfg(feature = "az")]
            impl az::UnwrappedCast<[<Decimal$x>]> for $int {
                #[inline]
                fn unwrapped_cast(self) -> [<Decimal$x>] {
                    az::cast(self)
                }
            }

            #[cfg(feature = "cast")]
            impl cast::From<[<Decimal$x>]> for $int {
                type Output = Result<Self, cast::Error>;

                fn cast(src: [<Decimal$x>]) -> Self::Output {
                    src.to_int_checked().ok_or_else(|| {
                        if src.is_nan() {
                            cast::Error::NaN
                        } else if src.is_infinite() {
                            cast::Error::Infinite
                        } else if src.is_sign_positive() {
                            cast::Error::Overflow
                        } else {
                            cast::Error::Underflow
                        }
                    })
                }
            }


            #[cfg(feature = "cast")]
            if_u512! { $int,
                {
                    // u512 overflows decimal32
                    only_32!($x,
                        impl cast::From<$int> for [<Decimal$x>] {
                            type Output = Result<Self, cast::Error>;

                            #[inline]
                            fn cast(src: $int) -> Self::Output {
                                // Even a u128 will never overflow a Decimal32's range
                                let result: Self = [<Decimal$x>]::from_int(src);

                                if result.is_finite() {
                                    Ok(result)
                                } else {
                                    Err(cast::Error::Overflow)
                                }
                            }
                        }
                    );

                    only_64_128!($x,
                        impl cast::From<$int> for [<Decimal$x>] {
                            type Output = Self;

                            #[inline]
                            fn cast(src: $int) -> Self::Output {
                                [<Decimal$x>]::from_int(src)
                            }
                        }
                    );
                },
                {
                    impl cast::From<$int> for [<Decimal$x>] {
                        type Output = Self;

                        #[inline]
                        fn cast(src: $int) -> Self::Output {
                            [<Decimal$x>]::from_int(src)
                        }
                    }
                }
            }

            #[cfg(feature = "num-traits")]
            impl num_traits::AsPrimitive<$int> for [<Decimal$x>] {
                #[inline]
                fn as_(self) -> $int {
                    self.to_int()
                }
            }

            #[cfg(feature = "num-traits")]
            impl num_traits::AsPrimitive<[<Decimal$x>]> for $int {
                #[inline]
                fn as_(self) -> [<Decimal$x>] {
                    [<Decimal$x>]::from_int(self)
                }
            }

            #[cfg(feature = "simba")]
            impl simba::scalar::SubsetOf<[<Decimal$x>]> for $int {
                #[inline]
                fn to_superset(&self) -> [<Decimal$x>] {
                    <Self as num_traits::AsPrimitive<[<Decimal$x>]>>::as_(*self)
                }

                #[inline]
                fn from_superset_unchecked(element: &[<Decimal$x>]) -> Self {
                    <[<Decimal$x>] as num_traits::AsPrimitive<Self>>::as_(*element)
                }

                #[inline]
                fn is_in_subset(_: &[<Decimal$x>]) -> bool {
                    true
                }
            }
        }
    };
}

conversion_traits!(
    (32, 64, 128),
    [
        (round_ties_even, TiesToEven, rnint),
        (ceil, TowardPositive, ceil),
        (floor, TowardNegative, floor),
        (trunc, TowardZero, int),
        (round, TiesToAway, rninta)
    ],
    [
        (u8, uint8, u32),
        (i8, int8, i32),
        (u16, uint16, u32),
        (i16, int16, i32)
    ],
    [(u32, uint32), (i32, int32)],
    [(u64, uint64), (i64, int64)],
    [(usize, UsizeEquiv), (isize, IsizeEquiv)],
    [
        (u128, (u128::MIN, 0_u128)),
        #[cfg(feature = "ethnum")]
        (ethnum::u256, (ethnum::u256::MIN, ethnum::u256::ZERO)),
        #[cfg(feature = "primitive-types")]
        (
            primitive_types::U128,
            (primitive_types::U128::zero(), primitive_types::U128::zero())
        ),
        #[cfg(feature = "primitive-types")]
        (
            primitive_types::U256,
            (primitive_types::U256::zero(), primitive_types::U256::zero())
        ),
        #[cfg(feature = "primitive-types")]
        (
            primitive_types::U512,
            (primitive_types::U512::zero(), primitive_types::U512::zero())
        )
    ],
    [
        (i128, (i128::MIN, 0_i128)),
        #[cfg(feature = "ethnum")]
        (ethnum::i256, (ethnum::i256::MIN, ethnum::i256::ZERO))
    ]
);

macro_rules! decimal_impls {
    ($($x:literal),*) => {$(
        paste! {
            /// A
            #[doc = $x "-bit"]
            /// decimal floating point type (specifically, the
            #[doc = "\"decimal" $x "\""]
            /// type defined in IEEE 754-2008, in its binary encoding).
            ///
            /// The decimal floats behave similarly to their binary equivalents (`f32` and `f64`) in most respects.
            /// NaN, infinities, and negative 0 work the same way.
            /// But instead of representing numbers as a multiple of a power of 2, this type
            /// is represented internally as a multiple of a power of 10.
            /// This means that any number that has few enough decimal digits to fit in the type
            /// can be represented exaclty. For example, binary floating point can't represent `0.1` exactly,
            /// but this type can.
            ///
            /// The downside of using decimal floating point is reduced performance, because most processors don't
            /// have dedicated instructions to handle them.
            ///
            /// In addition, the decimal floating point types generally have a wider range, but lower precision,
            /// compared to their binary equivalents.
            #[derive(Copy)]
            #[repr(transparent)]
            pub struct [<Decimal$x>] {
                inner: [<BID_UINT$x>],
            }

            #[allow(clippy::expl_impl_clone_on_copy)]
            impl Clone for [<Decimal$x>] {
                /// IEEE 754 5.5.1 **copy**
                #[doc(alias = "copy")]
                #[inline]
                fn clone(&self) -> Self { *self }
            }

            impl private::Sealed for [<Decimal$x>] {}

            impl convert::DecimalConvertFormat<f32> for [<Decimal$x>] {
                #[doc(hidden)]
                #[inline]
                fn convert_format(ctx: &mut Context, src: f32) -> Self {
                    let inner = unsafe {
                        [<__binary32_to_bid $x>](src, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                    };

                    Self { inner }
                }
            }

            impl convert::DecimalConvertFormat<f64> for [<Decimal$x>] {
                #[doc(hidden)]
                #[inline]
                fn convert_format(ctx: &mut Context, src: f64) -> Self {
                    let inner = unsafe {
                        [<__binary64_to_bid $x>](src, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                    };

                    Self { inner }
                }
            }

            impl convert::DecimalConvertFormat<[<Decimal$x>]> for f32 {
                #[doc(hidden)]
                #[inline]
                fn convert_format(ctx: &mut Context, src: [<Decimal$x>]) -> Self {
                    unsafe {
                        [<__bid $x _to_binary32>](src.inner, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                    }
                }
            }

            impl convert::DecimalConvertFormat<[<Decimal$x>]> for f64 {
                #[doc(hidden)]
                #[inline]
                fn convert_format(ctx: &mut Context, src: [<Decimal$x>]) -> Self {
                    unsafe {
                        [<__bid $x _to_binary64>](src.inner, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                    }
                }
            }

            only_64_128!($x,
                impl convert::DecimalConvertFormat<Decimal32> for [<Decimal$x>] {
                    #[doc(hidden)]
                    #[inline]
                    fn convert_format(ctx: &mut Context, src: Decimal32) -> Self {
                        let inner = unsafe {
                            [<__bid32_to_bid $x>](src.inner, ctx.flags.as_mut_ptr())
                        };

                        Self { inner }
                    }
                }
            );

            only_32!($x,
                impl convert::DecimalConvertFormat<Decimal64> for [<Decimal$x>] {
                    #[doc(hidden)]
                    #[inline]
                    fn convert_format(ctx: &mut Context, src: Decimal64) -> Self {
                        let inner = unsafe {
                            [<__bid64_to_bid $x>](src.inner, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                        };

                        Self { inner }
                    }
                }
            );

            only_128!($x,
                impl convert::DecimalConvertFormat<Decimal64> for [<Decimal$x>] {
                    #[doc(hidden)]
                    #[inline]
                    fn convert_format(ctx: &mut Context, src: Decimal64) -> Self {
                        let inner = unsafe {
                            [<__bid64_to_bid $x>](src.inner, ctx.flags.as_mut_ptr())
                        };

                        Self { inner }
                    }
                }
            );

            only_32_64!($x,
                impl convert::DecimalConvertFormat<Decimal128> for [<Decimal$x>] {
                    #[doc(hidden)]
                    #[inline]
                    fn convert_format(ctx: &mut Context, src: Decimal128) -> Self {
                        let inner = unsafe {
                            [<__bid128_to_bid $x>](src.inner, ctx.rounding.as_repr(), ctx.flags.as_mut_ptr())
                        };

                        Self { inner }
                    }
                }
            );

            // Canonicalizing operation
            impl convert::DecimalConvertFormat<[<Decimal$x>]> for [<Decimal$x>] {
                #[doc(hidden)]
                #[inline]
                fn convert_format(ctx: &mut Context, src: [<Decimal$x>]) -> Self {
                    const T: u32 = 15 * $x / 16 - 10;
                    const J: u32 = T / 10;
                    const MAX_PAYLOAD: [<u$x>] = (10 as [<u$x>]).pow(3 * J) - 1;

                    match src.class() {
                        Class::SignalingNan => {
                            ctx.flags = ctx.flags.union(Flags::INVALID_OPERATION);
                            let mut payload = src.to_bits() & ((1 << T) - 1);
                            if payload > MAX_PAYLOAD {
                                payload = 0;
                            }
                            [<Decimal$x>]::from_bits([<Decimal$x>]::SNAN.copysign(src).to_bits() | payload)

                        }
                        Class::QuietNan => {
                            let mut payload = src.to_bits() & ((1 << T) - 1);
                            if payload > MAX_PAYLOAD {
                                payload = 0;
                            }
                            [<Decimal$x>]::from_bits([<Decimal$x>]::NAN.copysign(src).to_bits() | payload)
                        },
                        Class::NegativeInfinite => Self::NEG_INFINITY,
                        Class::PositiveInfinite => Self::INFINITY,
                        _ => {
                            // see `integer_decode`
                            const MAX_SIGNIFICAND: [<u$x>] = (10 as [<u$x>]).pow(3 * J + 1) - 1;
                            const CASE_MASK: [<u$x>] = (0b11 << ($x - 3));
                            const CASE_1_SIGNIFICAND_MASK: [<u$x>] = (1 << (T + 3)) - 1;

                            let bits = src.to_bits();

                            let significand_mask: [<u$x>];
                            let significand: [<u$x>];
                            let result = (if (bits & CASE_MASK) != CASE_MASK {
                                // case i
                                significand = bits & CASE_1_SIGNIFICAND_MASK;
                                if significand > MAX_SIGNIFICAND {
                                    [<Decimal$x>]::from_bits(bits & !CASE_1_SIGNIFICAND_MASK)
                                } else {
                                    src
                                }
                            } else {
                                // case ii
                                significand_mask = (1 << (T + 1)) - 1;
                                significand = (bits & significand_mask) + (1 << (T + 3));
                                if significand > MAX_SIGNIFICAND {
                                    // Need to offset exponent to turn into case i form
                                    [<Decimal$x>]::from_bits((bits << 2) & !CASE_1_SIGNIFICAND_MASK).copysign(src)
                                } else {
                                    src
                                }
                            });

                            debug_assert_eq!(result, src);
                            result
                        }
                    }
                }
            }

            convert_format_impl_forward!($x, [f32, f64]);
            convert_format_impl_forward!($x -> [Decimal32, Decimal64, Decimal128]);

            #[cfg(feature = "cast")]
            const _: () = {
                impl_cast_no_overflow!(Decimal32, [<Decimal$x>]);
                impl_cast_no_overflow!(f32, [<Decimal$x>]);
                impl_cast_overflow!([<Decimal$x>], f32);

                #[cfg(feature = "half")]
                impl_cast_no_overflow!(half::f16, [<Decimal$x>]);

                #[cfg(feature = "half")]
                impl_cast_no_overflow!(half::bf16, [<Decimal$x>]);

                only_32!($x,
                    impl_cast_overflow!(f64, [<Decimal$x>]);
                    impl_cast_overflow!(Decimal64, [<Decimal$x>]);
                    impl_cast_no_overflow!([<Decimal$x>], f64);
                );

                only_32_64!($x,
                    impl_cast_overflow!(Decimal128, [<Decimal$x>]);
                );

                only_64_128!($x,
                    impl_cast_no_overflow!(f64, [<Decimal$x>]);
                    impl_cast_no_overflow!(Decimal64, [<Decimal$x>]);
                    impl_cast_overflow!([<Decimal$x>], f64)
                );

                only_128!($x,
                    impl_cast_no_overflow!(Decimal128, [<Decimal$x>]);
                );
            };

            // FIXME decimal -> f16, bf16
            #[cfg(feature = "half")]
            impl convert::DecimalConvertFormat<half::f16> for [<Decimal$x>] {
                fn convert_format(ctx: &mut Context, small: half::f16) -> [<Decimal$x>] {
                    ctx.convert_format(f32::from(small))
                }
            }

            #[cfg(feature = "half")]
            impl convert::DecimalConvertFormat<half::bf16> for [<Decimal$x>] {
                fn convert_format(ctx: &mut Context, small: half::bf16) -> [<Decimal$x>] {
                    ctx.convert_format(f32::from(small))
                }
            }

            #[cfg(feature = "half")]
            convert_format_impl_forward!($x <- nosubset [half::f16, half::bf16]);

            impl [<Decimal$x>] {
                decimal_op_forward!(
                    /// Returns the largest integer less than or equal to a number.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let f = d" $x "!(3.7);"]
                    #[doc = "let g = d" $x "!(3.0);"]
                    #[doc = "let h = d" $x "!(-3.7);"]
                    ///
                    #[doc = "assert_eq!(f.floor(), d" $x "!(3.0));"]
                    #[doc = "assert_eq!(g.floor(), d" $x "!(3.0));"]
                    #[doc = "assert_eq!(h.floor(), d" $x "!(-4.0));"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn floor(self) -> Self
                );

                decimal_op_forward!(
                    /// Returns the smallest integer greater than or equal to a number.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let f = d" $x "!(3.01);"]
                    #[doc = "let g = d" $x "!(4.0);"]
                    ///
                    #[doc = "assert_eq!(f.ceil(), d" $x "!(4.0));"]
                    #[doc = "assert_eq!(g.ceil(), d" $x "!(4.0));"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn ceil(self) -> Self
                );

                decimal_op_forward!(
                    /// Returns the nearest integer to a number. Round half-way cases away from
                    /// `0.0`.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let f = d" $x "!(3.3);"]
                    #[doc = "let g = d" $x "!(-3.3);"]
                    ///
                    #[doc = "assert_eq!(f.round(), d" $x "!(3.0));"]
                    #[doc = "assert_eq!(g.round(), d" $x "!(-3.0));"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn round(self) -> Self
                );

                // TODO name
                decimal_op_forward!(
                    /// Returns the nearest integer to a number. Round half-way cases to the number
                    /// with an even least significant digit.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let f = d" $x "!(3.3);"]
                    #[doc = "let g = d" $x "!(-3.3);"]
                    ///
                    #[doc = "assert_eq!(f.round(), d" $x "!(3.0));"]
                    #[doc = "assert_eq!(g.round(), d" $x "!(-3.0));"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn round_ties_even(self) -> Self
                );

                decimal_op_forward!(
                    /// Returns the integer part of a number.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let f = d" $x "!(3.7);"]
                    #[doc = "let g = d" $x "!(3.0);"]
                    #[doc = "let h = d" $x "!(-3.7);"]
                    ///
                    #[doc = "assert_eq!(f.trunc(), d" $x "!(3.0));"]
                    #[doc = "assert_eq!(g.trunc(), d" $x "!(3.0));"]
                    #[doc = "assert_eq!(h.trunc(), d" $x "!(-3.0));"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn trunc(self) -> Self
                );

                /// Returns the fractional part of a number.
                ///
                /// # Examples
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let x = d" $x "!(3.6);"]
                #[doc = "let y = d" $x "!(-3.6);"]
                #[doc = "let abs_difference_x = (x.fract() - d" $x "!(0.6)).abs();"]
                #[doc = "let abs_difference_y = (y.fract() - d" $x "!(-0.6)).abs();"]
                ///
                #[doc = "assert!(abs_difference_x <= Decimal" $x "::EPSILON);"] // FIXME use error?
                #[doc = "assert!(abs_difference_y <= Decimal" $x "::EPSILON);"]
                /// ```
                #[must_use = "method returns a new number and does not mutate the original value"]
                #[inline]
                pub fn fract(self) -> Self {
                    self - self.trunc()
                }


                /// Computes the absolute value of `self`. Returns `NAN` if the
                /// number is `NAN`.
                ///
                /// IEEE 754 5.5.1 **abs**
                ///
                /// # Examples
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let x = d" $x "!(3.5);"]
                #[doc = "let y = d" $x "!(-3.5);"]
                ///
                /// let abs_difference_x = (x.abs() - x).abs();
                /// let abs_difference_y = (y.abs() - (-y)).abs();
                ///
                #[doc = "assert!(abs_difference_x <= Decimal" $x "::EPSILON);"] // FIXME use error?
                #[doc = "assert!(abs_difference_y <= Decimal" $x "::EPSILON);"]
                ///
                #[doc = "assert!(Decimal" $x "::NAN.abs().is_nan());"]
                /// ```
                #[must_use = "method returns a new number and does not mutate the original value"]
                #[inline]
                pub const fn abs(self) -> Self {
                    const SIGN_MASK: [<u$x>] = 1 << ($x - 1);
                    Self::from_bits(self.to_bits() & !SIGN_MASK)
                }


                /// Returns a number that represents the sign of `self`.
                ///
                /// - `1.0` if the number is positive, `+0.0` or `INFINITY`
                /// - `-1.0` if the number is negative, `-0.0` or `NEG_INFINITY`
                /// - `NAN` if the number is `NAN`
                ///
                /// # Examples
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let f = d" $x "!(3.5);"]
                ///
                #[doc = "assert_eq!(f.signum(), d" $x "!(1.0));"]
                #[doc = "assert_eq!(Decimal" $x "::NEG_INFINITY.signum(), d" $x "!(-1.0));"]
                ///
                #[doc = "assert!(Decimal" $x "::NAN.signum().is_nan());"]
                /// ```
                #[must_use = "method returns a new number and does not mutate the original value"]
                #[inline]
                pub const fn signum(self) -> Self {
                    if self.is_nan() { Self::NAN } else { [<d$x>]!(1).copysign(self) }
                }

                /// Returns a number composed of the magnitude of `self` and the sign of
                /// `sign`.
                ///
                /// Equal to `self` if the sign of `self` and `sign` are the same, otherwise
                /// equal to `-self`. If `self` is a `NAN`, then a `NAN` with the sign of
                /// `sign` is returned.
                ///
                /// IEEE 754 5.5.1 **copySign**
                ///
                /// # Examples
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let f = d" $x "!(3.5);"]
                ///
                #[doc = "assert_eq!(f.copysign(d" $x "!(0.42)), d" $x "!(3.5));"]
                #[doc = "assert_eq!(f.copysign(d" $x "!(-0.42)), d" $x "!(-3.5));"]
                #[doc = "assert_eq!((-f).copysign(d" $x "!(0.42)), d" $x "!(3.5));"]
                #[doc = "assert_eq!((-f).copysign(d" $x "!(-0.42)), d" $x "!(-3.5));"]
                ///
                #[doc = "assert!(Decimal" $x "::NAN.copysign(d" $x "!(1.0)).is_nan());"]
                /// ```
                #[doc(alias = "copySign")]
                #[must_use = "method returns a new number and does not mutate the original value"]
                #[inline]
                pub const fn copysign(self, sign: Self) -> Self {
                    const SIGN_MASK: [<u$x>] = 1 << ($x - 1);
                    Self::from_bits((self.to_bits() & !SIGN_MASK) | (sign.to_bits() & SIGN_MASK))
                }

                decimal_op_forward!(
                    /// Fused multiply-add. Computes `(self * a) + b` with only one rounding
                    /// error, yielding a more accurate result than an unfused multiply-add.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let m = d" $x "!(10.0);"]
                    #[doc = "let x = d" $x "!(4.0);"]
                    #[doc = "let b = d" $x "!(60.0);"]
                    ///
                    /// // 100.0
                    /// let abs_difference = (m.mul_add(x, b) - ((m * x) + b)).abs();
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn mul_add(self, a: Self, b: Self) -> Self
                );

                /// Calculates Euclidean division, the matching method for `rem_euclid`.
                ///
                /// This computes the integer `n` such that
                /// `self = n * rhs + self.rem_euclid(rhs)`.
                /// In other words, the result is `self / rhs` rounded to the integer `n`
                /// such that `self >= n * rhs`.
                ///
                /// # Examples
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let a = d" $x "!(7.0);"]
                #[doc = "let b = d" $x "!(4.0);"]
                #[doc = "assert_eq!(a.div_euclid(b), d" $x "!(1.0)); // 7.0 > 4.0 * 1.0"]
                #[doc = "assert_eq!((-a).div_euclid(b), d" $x "!(-2.0)); // -7.0 >= 4.0 * -2.0"]
                #[doc = "assert_eq!(a.div_euclid(-b), d" $x "!(-1.0)); // 7.0 >= -4.0 * -1.0"]
                #[doc = "assert_eq!((-a).div_euclid(-b), d" $x "!(2.0)); // -7.0 >= -4.0 * 2.0"]
                /// ```
                #[must_use = "method returns a new number and does not mutate the original value"]
                #[inline]
                pub fn div_euclid(self, rhs: Self) -> Self {
                    let q = (self / rhs).trunc();
                    if self % rhs < [<d$x>]!(0) {
                        return if rhs > [<d$x>]!(0) { q - [<d$x>]!(1) } else { q + [<d$x>]!(1) };
                    }
                    q
                }

                /// Calculates the least nonnegative remainder of `self (mod rhs)`.
                ///
                /// In particular, the return value `r` satisfies `0.0 <= r < rhs.abs()` in
                /// most cases. However, due to a floating point round-off error it can
                /// result in `r == rhs.abs()`, violating the mathematical definition, if
                /// `self` is much smaller than `rhs.abs()` in magnitude and `self < 0.0`.
                /// This result is not an element of the function's codomain, but it is the
                /// closest floating point number in the real numbers and thus fulfills the
                /// property `self == self.div_euclid(rhs) * rhs + self.rem_euclid(rhs)`
                /// approximatively.
                ///
                /// # Examples
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let a = d" $x "!(7.0);"]
                #[doc = "let b = d" $x "!(4.0);"]
                #[doc = "assert_eq!(a.rem_euclid(b), d" $x "!(3.0));"]
                #[doc = "assert_eq!((-a).rem_euclid(b), d" $x "!(1.0));"]
                #[doc = "assert_eq!(a.rem_euclid(-b), d" $x "!(3.0));"]
                #[doc = "assert_eq!((-a).rem_euclid(-b), d" $x "!(1.0));"]
                /// // limitation due to round-off error
                #[doc = "assert!((-Decimal" $x "::EPSILON).rem_euclid(d" $x "!(3.0)) != d" $x "!(0.0));"]
                /// ```
                #[must_use = "method returns a new number and does not mutate the original value"]
                #[inline]
                pub fn rem_euclid(self, rhs: Self) -> Self {
                    let r = self % rhs;
                    if r < [<d$x>]!(0) { r + rhs.abs() } else { r }
                }


                /// Raises a number to an integer power.
                ///
                /// # Examples
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let x = d" $x "!(2.0);"]
                /// let abs_difference = (x.powi(2) - (x * x)).abs();
                ///
                #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                /// ```
                #[must_use = "method returns a new number and does not mutate the original value"]
                #[inline]
                pub fn powi(self, n: i32) -> Self {
                    self.powf(Self::from_int(n))
                }

                decimal_op_forward!(
                    /// Raises a number to a floating point power.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(2.0);"]
                    #[doc = "let abs_difference = (x.powf(d" $x "!(2.0)) - (x * x)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn powf(self, n: Self) -> Self
                );

                decimal_op_forward!(
                    /// Returns the square root of a number.
                    ///
                    /// Returns NaN if `self` is a negative number other than `-0.0`.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let positive = d" $x "!(4.0);"]
                    #[doc = "let negative = d" $x "!(-4.0);"]
                    ///
                    #[doc = "let abs_difference = (positive.sqrt() - d" $x "!(2.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// assert!(negative.sqrt().is_nan());
                    #[doc = "assert!(d" $x "!(-0).sqrt() == d" $x "!(-0));"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn sqrt(self) -> Self
                );

                decimal_op_forward!(
                    /// Returns `e^(self)`, (the exponential function).
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    /// // e^1
                    #[doc = "let e = d" $x "!(1).exp();"]
                    ///
                    /// // ln(e) - 1 == 0
                    #[doc = "let abs_difference = (e.ln() - d" $x "!(1)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn exp(self) -> Self
                );

                decimal_op_forward!(
                    /// Returns `2^(self)`.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let f = d" $x "!(2.0);"]
                    ///
                    /// // 2^2 - 4 == 0
                    #[doc = "let abs_difference = (f.exp2() - d" $x "!(4.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn exp2(self) -> Self
                );

                decimal_op_forward!(
                    /// Returns the natural logarithm of the number.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    /// // e^1
                    #[doc = "let e = d" $x "!(1).exp();"]
                    ///
                    /// // ln(e) - 1 == 0
                    #[doc = "let abs_difference = (e.ln() - d" $x "!(1)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn ln(self) -> Self
                );

                /// Returns the logarithm of the number with respect to an arbitrary base.
                ///
                /// The result might not be correctly rounded owing to implementation details;
                /// `self.log2()` can produce more accurate results for base 2, and
                /// `self.log10()` can produce more accurate results for base 10.
                ///
                /// # Examples
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let twenty_five = d" $x "!(25.0);"]
                ///
                /// // log5(25) - 2 == 0
                #[doc = "let abs_difference = (twenty_five.log(d" $x "!(5.0)) - d" $x "!(2.0)).abs();"]
                ///
                #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                /// ```
                #[must_use = "method returns a new number and does not mutate the original value"]
                #[inline]
                pub fn log(self, base: Self) -> Self {
                    self.ln() / base.ln()
                }

                decimal_op_forward!(
                    /// Returns the base 2 logarithm of the number.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let four = d" $x "!(4.0);"]
                    ///
                    /// // log2(4) - 2 == 0
                    #[doc = "let abs_difference = (four.log2() - d" $x "!(2.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn log2(self) -> Self
                );

                decimal_op_forward!(
                    /// Returns the base 10 logarithm of the number.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let hundred = d" $x "!(100.0);"]
                    ///
                    /// // log10(100) - 2 == 0
                    #[doc = "let abs_difference = (hundred.log10() - d" $x "!(2.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn log10(self) -> Self
                );

                decimal_op_forward!(
                    /// The positive difference of two numbers.
                    ///
                    /// * If `self <= other`: `0:0`
                    /// * Else: `self - other`
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(3.0);"]
                    #[doc = "let y = d" $x "!(-3.0);"]
                    ///
                    #[doc = "let abs_difference_x = (x.abs_sub(d" $x "!(1.0)) - d" $x "!(2.0)).abs();"]
                    #[doc = "let abs_difference_y = (y.abs_sub(d" $x "!(1.0)) - d" $x "!(0.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference_x <= Decimal" $x "::EPSILON);"]
                    #[doc = "assert!(abs_difference_y <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    #[deprecated = "the corresponding `std` method on `f32` and `f64` \
                                    was deprecated, because it's terribly named. \
                                    You probably meant `(self - other).abs()`, \
                                    but this is `(self - other).max(0.0)` \
                                    except that `abs_sub` also propagates NaNs (also \
                                    known as `fdim` in C). We expose this method \
                                    because the underlying Intel library has it, \
                                    and maybe you need it. But you probably don't."
                    ]
                    pub fn abs_sub(self, other: Self) -> Self
                );

                decimal_op_forward!(
                    /// Returns the cube root of a number.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(8.0);"]
                    ///
                    /// // x^(1/3) - 2 == 0
                    #[doc = "let abs_difference = (x.cbrt() - d" $x "!(2.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn cbrt(self) -> Self
                );

                decimal_op_forward!(
                    /// Calculates the length of the hypotenuse of a right-angle triangle given
                    /// legs of length `x` and `y`.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(3.0);"]
                    #[doc = "let y = d" $x "!(4.0);"]
                    ///
                    /// // sqrt(x^2 + y^2)
                    #[doc = "let abs_difference = (x.hypot(y) - d" $x "!(5.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn hypot(self, other: Self) -> Self
                );

                decimal_op_forward!(
                    /// Computes the sine of a number (in radians).
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = decimalfp::decimal" $x "::consts::FRAC_PI_2;"]
                    ///
                    #[doc = "let abs_difference = (x.sin() - d" $x "!(1.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn sin(self) -> Self
                );

                decimal_op_forward!(
                    /// Computes the cosine of a number (in radians).
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(2.0) * decimalfp::decimal" $x "::consts::PI;"]
                    ///
                    #[doc = "let abs_difference = (x.cos() - d" $x "!(1.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn cos(self) -> Self
                );

                decimal_op_forward!(
                    /// Computes the tangent of a number (in radians).
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = decimalfp::decimal" $x "::consts::FRAC_PI_4;"]
                    #[doc = "let abs_difference = (x.tan() - d" $x "!(1.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn tan(self) -> Self
                );

                decimal_op_forward!(
                    /// Computes the arcsine of a number. Return value is in radians in
                    /// the range [-pi/2, pi/2] or NaN if the number is outside the range
                    /// [-1, 1].
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let f = decimalfp::decimal" $x "::consts::FRAC_PI_2;"]
                    ///
                    /// // asin(sin(pi/2))
                    #[doc = "let abs_difference = (f.sin().asin() -  decimalfp::decimal" $x "::consts::FRAC_PI_2).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn asin(self) -> Self
                );

                decimal_op_forward!(
                    /// Computes the arccosine of a number. Return value is in radians in
                    /// the range [0, pi] or NaN if the number is outside the range
                    /// [-1, 1].
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let f = decimalfp::decimal" $x "::consts::FRAC_PI_4;"]
                    ///
                    /// // acos(cos(pi/4))
                    #[doc = "let abs_difference = (f.cos().acos() -  decimalfp::decimal" $x "::consts::FRAC_PI_4).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn acos(self) -> Self
                );

                decimal_op_forward!(
                    /// Computes the arctangent of a number. Return value is in radians in the
                    /// range [-pi/2, pi/2];
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let f = d" $x "!(1.0);"]
                    ///
                    /// // atan(tan(1))
                    #[doc = "let abs_difference = (f.tan().atan() -  d" $x "!(1.0)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn atan(self) -> Self
                );

                decimal_op_forward!(
                    /// Computes the four quadrant arctangent of `self` (`y`) and `other` (`x`) in radians.
                    ///
                    /// * `x = 0`, `y = 0`: `0`
                    /// * `x >= 0`: `arctan(y/x)` -> `[-pi/2, pi/2]`
                    /// * `y >= 0`: `arctan(y/x) + pi` -> `(pi/2, pi]`
                    /// * `y < 0`: `arctan(y/x) - pi` -> `(-pi, -pi/2)`
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    /// // Positive angles measured counter-clockwise
                    /// // from positive x axis
                    /// // -pi/4 radians (45 deg clockwise)
                    #[doc = "let x1 = d" $x "!(3.0);"]
                    #[doc = "let y1 = d" $x "!(-3.0);"]
                    ///
                    /// // 3pi/4 radians (135 deg counter-clockwise)
                    #[doc = "let x2 = d" $x "!(-3.0);"]
                    #[doc = "let y2 = d" $x "!(3.0);"]
                    ///
                    #[doc = "let abs_difference_1 = (y1.atan2(x1) -  (-decimalfp::decimal" $x "::consts::FRAC_PI_4)).abs();"]
                    #[doc = "let abs_difference_2 = (y2.atan2(x2) -  (d" $x "!(3.0) * decimalfp::decimal" $x "::consts::FRAC_PI_4)).abs();"]
                    ///
                    #[doc = "assert!(abs_difference_1 <= Decimal" $x "::EPSILON);"]
                    #[doc = "assert!(abs_difference_2 <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn atan2(self, other: Self) -> Self
                );

                /// Simultaneously computes the sine and cosine of the number, `x`. Returns
                /// `(sin(x), cos(x))`
                ///
                /// # Examples
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let x = decimalfp::decimal" $x "::consts::FRAC_PI_4;"]
                /// let f = x.sin_cos();
                ///
                /// assert_eq!(f.0, x.sin());
                /// assert_eq!(f.1, x.cos());
                /// ```
                #[must_use]
                #[inline]
                pub fn sin_cos(self) -> (Self, Self) {
                    (self.sin(), self.cos())
                }

                decimal_op_forward!(
                    /// Returns `e^(self) - 1` in a way that is accurate even if the
                    /// number is close to zero.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(1e-16);"]
                    ///
                    /// // for very small x, e^x is approximately 1 + x + x^2 / 2
                    #[doc = "let approx = x + x * x /d" $x "!(2.0);"]
                    /// let abs_difference = (x.exp_m1() - approx).abs();
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn exp_m1(self) -> Self
                );

                decimal_op_forward!(
                    /// Returns `ln(1+n)` (natural logarithm) more accurately than if
                    /// the operations were performed separately.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(1e-16);"]
                    ///
                    /// // for very small x, ln(1 + x) is approximately x - x^2 / 2
                    #[doc = "let approx = x - x * x /d" $x "!(2.0);"]
                    /// let abs_difference = (x.ln_1p() - approx).abs();
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn ln_1p(self) -> Self
                );

                decimal_op_forward!(
                    /// Hyperbolic sine function.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let e = decimalfp::decimal" $x "::consts::E;"]
                    #[doc = "let x = d" $x "!(1.0);"]
                    ///
                    /// let f = x.sinh();
                    /// // Solving sinh() at 1 gives `(e^2-1)/(2e)`
                    #[doc = "let g = ((e * e) - d" $x "!(1.0)) / (d" $x "!(2.0) * e);"]
                    /// let abs_difference = (f - g).abs();
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn sinh(self) -> Self
                );

                decimal_op_forward!(
                    /// Hyperbolic cosine function.
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let e = decimalfp::decimal" $x "::consts::E;"]
                    #[doc = "let x = d" $x "!(1.0);"]
                    /// let f = x.cosh();
                    /// // Solving cosh() at 1 gives this result
                    #[doc = "let g = ((e * e) + d" $x "!(1.0)) / (d" $x "!(2.0) * e);"]
                    /// let abs_difference = (f - g).abs();
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn cosh(self) -> Self
                );

                decimal_op_forward!(
                    /// Hyperbolic tangent function.
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let e = decimalfp::decimal" $x "::consts::E;"]
                    #[doc = "let x = d" $x "!(1.0);"]
                    ///
                    /// let f = x.tanh();
                    /// // Solving tanh() at 1 gives `(1 - e^(-2))/(1 + e^(-2))`
                    #[doc = "let g = (d" $x "!(1.0) - e.powi(-2)) / (d" $x "!(1.0) + e.powi(-2));"]
                    /// let abs_difference = (f - g).abs();
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn tanh(self) -> Self
                );

                decimal_op_forward!(
                    /// Inverse hyperbolic sine function.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(1.0);"]
                    /// let f = x.sinh().asinh();
                    ///
                    #[doc = "let abs_difference = (f - x).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn asinh(self) -> Self
                );

                decimal_op_forward!(
                    /// Inverse hyperbolic cosine function.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(1.0);"]
                    /// let f = x.cosh().acosh();
                    ///
                    #[doc = "let abs_difference = (f - x).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn acosh(self) -> Self
                );

                decimal_op_forward!(
                    /// Inverse hyperbolic tangent function.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let e = decimalfp::decimal" $x "::consts::E;"]
                    /// let f = e.tanh().atanh();
                    ///
                    #[doc = "let abs_difference = (f - e).abs();"]
                    ///
                    #[doc = "assert!(abs_difference <= d" $x "!(10) * Decimal" $x "::EPSILON);"]
                    /// ```
                    #[must_use = "method returns a new number and does not mutate the original value"]
                    pub fn atanh(self) -> Self
                );
            }

            pub mod [<decimal$x>] {
                //! Contains mathematical constants for the decimal type.

                /// Basic mathematical constants.
                pub mod consts {
                    use crate::*;

                    /// Archimedes' constant (π)
                    pub const PI: [<Decimal$x>] = per_width!($x, d32!(3.141593), d64!(3.141592653589793), d128!(3.141592653589793238462643383279503));

                    /// The full circle constant (τ)
                    ///
                    /// Equal to 2π.
                    pub const TAU: [<Decimal$x>] = per_width!($x, d32!(6.283185), d64!(6.283185307179586), d128!(6.283185307179586476925286766559006));

                    /// π/2
                    pub const FRAC_PI_2: [<Decimal$x>] = per_width!($x, d32!(1.570796), d64!(1.570796326794897), d128!(1.570796326794896619231321691639751));

                    /// π/3
                    pub const FRAC_PI_3: [<Decimal$x>] = per_width!($x, d32!(1.047198), d64!(1.047197551196598), d128!(1.047197551196597746154214461093168));

                    /// π/4
                    pub const FRAC_PI_4: [<Decimal$x>] = per_width!($x, d32!(0.7853982), d64!(0.7853981633974483), d128!(0.7853981633974483096156608458198757));

                    /// π/6
                    pub const FRAC_PI_6: [<Decimal$x>] = per_width!($x, d32!(0.5235988), d64!(0.5235987755982989), d128!(0.5235987755982988730771072305465838));

                    /// π/8
                    pub const FRAC_PI_8: [<Decimal$x>] = per_width!($x, d32!(0.3926991), d64!(0.3926990816987242), d128!(0.3926990816987241548078304229099379));

                    /// π/180
                    pub const FRAC_PI_180: [<Decimal$x>] = per_width!($x, d32!(0.01745329), d64!( 0.01745329251994330), d128!(0.01745329251994329576923690768488613));

                    /// 1/π
                    pub const FRAC_1_PI: [<Decimal$x>] = per_width!($x, d32!(0.3183099), d64!(0.3183098861837907), d128!(0.3183098861837906715377675267450287));

                    /// 2/π
                    pub const FRAC_2_PI: [<Decimal$x>] = per_width!($x, d32!(0.6366198), d64!(0.6366197723675813), d128!(0.6366197723675813430755350534900574));

                    /// 180/π
                    pub const FRAC_180_PI: [<Decimal$x>] = per_width!($x, d32!(57.29578), d64!(57.29577951308232), d128!(57.29577951308232087679815481410517));

                    /// 2/sqrt(π)
                    pub const FRAC_2_SQRT_PI: [<Decimal$x>] = per_width!($x, d32!(1.128379), d64!(1.128379167095513), d128!(1.128379167095512573896158903121545));

                    /// sqrt(2)
                    pub const SQRT_2: [<Decimal$x>] = per_width!($x, d32!(1.414214), d64!(1.414213562373095), d128!(1.414213562373095048801688724209698));

                    /// 1/sqrt(2)
                    pub const FRAC_1_SQRT_2: [<Decimal$x>] = per_width!($x, d32!(0.7071068), d64!(0.7071067811865475), d128!(0.7071067811865475244008443621048490));

                    /// Euler's number (e)
                    pub const E: [<Decimal$x>] = per_width!($x, d32!(2.718282), d64!(2.718281828459045), d128!(2.718281828459045235360287471352662));

                    /// log<sub>2</sub>(10)
                    pub const LOG2_10: [<Decimal$x>] = per_width!($x, d32!(3.321928), d64!(3.321928094887362), d128!(3.321928094887362347870319429489390));

                    /// log<sub>2</sub>(e)
                    pub const LOG2_E: [<Decimal$x>] = per_width!($x, d32!(1.442695), d64!(1.442695040888963), d128!(1.442695040888963407359924681001892));

                    /// log<sub>10</sub>(2)
                    pub const LOG10_2: [<Decimal$x>] = per_width!($x, d32!(0.3010300), d64!(0.3010299956639812), d128!(0.3010299956639811952137388947244930));

                    /// log<sub>10</sub>(e)
                    pub const LOG10_E: [<Decimal$x>] = per_width!($x, d32!(0.4342945), d64!(0.4342944819032518), d128!(0.4342944819032518276511289189166051));

                    /// ln(2)
                    pub const LN_2: [<Decimal$x>] = per_width!($x, d32!(0.6931472), d64!(0.6931471805599453), d128!(0.6931471805599453094172321214581766));

                    /// ln(10)
                    pub const LN_10: [<Decimal$x>] = per_width!($x, d32!(2.302585), d64!(2.302585092994046), d128!(2.302585092994045684017991454684364));
                }
            }

            // Values from ISO/IEC TR 24732:2009 latest draft (http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1312.pdf)

            impl [<Decimal$x>] {
                /// The radix or base of the internal representation of
                #[doc = "`Decimal" $x "`."]
                ///
                /// IEEE 754 5.7.2 **radix**
                #[doc(alias = "radix")]
                pub const RADIX: u32 = 10;

                /// Number of significant digits in base 10.
                pub const MANTISSA_DIGITS: u32 = per_width!($x, 7, 16, 34);

                // TODO https://github.com/rust-lang/rust/pull/89238
                /// Number of significant digits in base 10.
                pub const DIGITS: u32 = [<Decimal$x>]::MANTISSA_DIGITS;

                /// [Machine epsilon] value for
                #[doc = "`Decimal" $x "`."]
                ///
                /// This is the difference between `1.0` and the next larger representable number.
                ///
                /// [Machine epsilon]: https://en.wikipedia.org/wiki/Machine_epsilon
                pub const EPSILON: [<Decimal$x>] = per_width!($x, d32!(1E-6), d64!(1E-15), d128!(1E-33));

                /// Most negative
                #[doc = "`Decimal" $x "`"]
                /// value.
                pub const MIN: [<Decimal$x>] = per_width!($x, d32!(-9999999E+90), d64!(-9999999999999999E+369), d128!(-9999999999999999999999999999999999E+6111));

                /// Smallest positive non-subnormal finite
                #[doc = "`Decimal" $x "`"]
                /// value.
                pub const MIN_POSITIVE: [<Decimal$x>] = per_width!($x, d32!(1E-95), d64!(1E-383), d128!(1E-6143));

                /// Smallest positive subnormal
                #[doc = "`Decimal" $x "`"]
                /// value.
                #[doc(alias = "MIN_POSITIVE_SUBNORMAL")]
                pub const SUBNORMAL_MIN_POSITIVE: [<Decimal$x>] = per_width!($x, d32!(1E-101), d64!(1E-398), d128!(1E-6176));

                /// Largest finite
                #[doc = "`Decimal" $x "`"]
                /// value.
                pub const MAX: [<Decimal$x>] = per_width!($x, d32!(9999999E+90), d64!(9999999999999999E+369), d128!(9999999999999999999999999999999999E+6111));

                /// One greater than the minimum possible normal power of 10 exponent.
                pub const MIN_EXP: i32 = per_width!($x, -94, -382, 142);

                /// Maximum possible power of 10 exponent.
                pub const MAX_EXP: i32 = per_width!($x, 97, 385, 6145);

                // Self::MIN_POSITIVE.log2().ceil()
                /// Minimum possible normal power of 2 exponent.
                pub const MIN_2_EXP: i32 = per_width!($x, -315, -1272, -20406);

                // Self::MAX.log2().floor()
                /// Maximum possible power of 2 exponent.
                pub const MAX_2_EXP: i32 = per_width!($x, 322, 1278, 20413);

                /// Minimum possible normal power of 10 exponent.
                pub const MIN_10_EXP: i32 = per_width!($x, -95, -383, -6143);

                /// Maximum possible power of 10 exponent.
                pub const MAX_10_EXP: i32 = per_width!($x, 97, 385, 6145);

                /// Not a Number (NaN).
                pub const NAN: [<Decimal$x>] = Self::from_bits(per_width!($x,
                    0x7C000000,
                    0x7C00000000000000,
                    0x7C000000000000000000000000000000
                ));

                /// Negative Not a Number (NaN).
                pub const NEG_NAN: [<Decimal$x>] = Self::from_bits(per_width!($x,
                    0xFC000000,
                    0xFC00000000000000,
                    0xFC000000000000000000000000000000
                ));

                /// Signaling Not a Number (sNaN).
                pub const SNAN: [<Decimal$x>] = Self::from_bits(per_width!($x,
                    0x7E000000,
                    0x7E00000000000000,
                    0x7E000000000000000000000000000000
                ));

                /// Negative signaling Not a Number (sNaN).
                pub const NEG_SNAN: [<Decimal$x>] = Self::from_bits(per_width!($x,
                    0xFE000000,
                    0xFE00000000000000,
                    0xFE000000000000000000000000000000
                ));

                /// Infinity (∞).
                pub const INFINITY: [<Decimal$x>] = Self::from_bits(per_width!($x,
                    0x78000000,
                    0x7800000000000000,
                    0x78000000000000000000000000000000
                ));

                /// Negative infinity (−∞).
                pub const NEG_INFINITY: [<Decimal$x>] = Self::from_bits(per_width!($x,
                    0xF8000000,
                    0xF800000000000000,
                    0xF8000000000000000000000000000000
                ));

                // FIXME constify more trivial functions from bidxx_noncomp.c


                /// Returns `true` if this value is `NaN`.
                ///
                /// IEEE 754 5.7.2 **isNaN**
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let nan = Decimal" $x "::NAN;"]
                #[doc = "let snan = Decimal" $x "::SNAN;"]
                #[doc = "let d = d" $x "!(7.0);"]
                ///
                /// assert!(nan.is_nan());
                /// assert!(snan.is_nan());
                /// assert!(!d.is_nan());
                /// ```
                #[doc(alias = "isNaN")]
                #[must_use]
                #[inline]
                pub const fn is_nan(self) -> bool {
                    const NAN_MASK: [<u$x>] = 0x7c << ($x - 8);
                    (self.to_bits() & NAN_MASK) == NAN_MASK
                }

                /// Returns `true` if this value is positive infinity or negative infinity, and
                /// `false` otherwise.
                ///
                /// IEEE 754 5.7.2 **isInfinite**
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let d = d" $x "!(7.0);"]
                #[doc = "let inf = Decimal" $x "::INFINITY;"]
                #[doc = "let neg_inf = Decimal" $x "::NEG_INFINITY;"]
                #[doc = "let nan = Decimal" $x "::NAN;"]
                ///
                /// assert!(!d.is_infinite());
                /// assert!(!nan.is_infinite());
                ///
                /// assert!(inf.is_infinite());
                /// assert!(neg_inf.is_infinite());
                /// ```
                #[doc(alias = "isInfinite")]
                #[must_use]
                #[inline]
                pub const fn is_infinite(self) -> bool {
                    const INF_MASK: [<u$x>] = 0x78 << ($x - 8);
                    ((self.to_bits() & INF_MASK) == INF_MASK) && !self.is_nan()
                }

                decimal_op_simple_bool!($x,
                    /// Returns `true` if this number is positive or negative zero.
                    ///
                    /// IEEE 754 5.7.2 **isZero**
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let d = d" $x "!(7.0);"]
                    #[doc = "let zero = d" $x "!(0);"]
                    #[doc = "let neg_zero = d" $x "!(-0);"]
                    #[doc = "let nan = Decimal" $x "::NAN;"]
                    ///
                    /// assert!(!d.is_zero());
                    /// assert!(!nan.is_zero());
                    ///
                    /// assert!(zero.is_zero());
                    /// assert!(neg_zero.is_zero());
                    /// ```
                    #[doc(alias = "isZero")]
                    #[must_use]
                    pub fn is_zero { isZero }
                );

                /// Returns `true` if this number is neither infinite nor `NaN`.
                ///
                /// IEEE 754 5.7.2 **isFinite**
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let d = d" $x "!(7.0);"]
                #[doc = "let inf = Decimal" $x "::INFINITY;"]
                #[doc = "let neg_inf = Decimal" $x "::NEG_INFINITY;"]
                #[doc = "let nan = Decimal" $x "::NAN;"]
                ///
                /// assert!(d.is_finite());
                ///
                /// assert!(!nan.is_finite());
                /// assert!(!inf.is_finite());
                /// assert!(!neg_inf.is_finite());
                /// ```
                #[doc(alias = "isFinite")]
                #[must_use]
                pub const fn is_finite(self) -> bool {
                    const INF_MASK: [<u$x>] = 0x78 << ($x - 8);
                    (self.to_bits() & INF_MASK) != INF_MASK
                }

                decimal_op_simple_bool!($x,
                    /// Returns `true` if the number is [subnormal].
                    ///
                    /// IEEE 754 5.7.2 **isSubnormal**
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let min = Decimal" $x "::MIN_POSITIVE;"]
                    #[doc = "let max = Decimal" $x "::MAX;"]
                    #[doc = "let lower_than_min = Decimal" $x "::SUBNORMAL_MIN_POSITIVE;"]
                    #[doc = "let zero = d" $x "!(0);"]
                    ///
                    /// assert!(!min.is_subnormal());
                    /// assert!(!max.is_subnormal());
                    ///
                    /// assert!(!zero.is_subnormal());
                    #[doc = "assert!(!Decimal" $x "::NAN.is_subnormal());"]
                    #[doc = "assert!(!Decimal" $x "::INFINITY.is_subnormal());"]
                    /// // Values between `0` and `min` are Subnormal.
                    /// assert!(lower_than_min.is_subnormal());
                    /// ```
                    /// [subnormal]: https://en.wikipedia.org/wiki/Denormal_number
                    #[doc(alias = "isSubnormal")]
                    #[must_use]
                    pub fn is_subnormal { isSubnormal }
                );

                decimal_op_simple_bool!($x,
                    /// Returns `true` if the number is neither zero, infinite,
                    /// [subnormal], or `NaN`.
                    ///
                    /// IEEE 754 5.7.2 **isNormal**
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let min = Decimal" $x "::MIN_POSITIVE;"]
                    #[doc = "let max = Decimal" $x "::MAX;"]
                    #[doc = "let lower_than_min = Decimal" $x "::SUBNORMAL_MIN_POSITIVE;"]
                    #[doc = "let zero = d" $x "!(0);"]
                    ///
                    /// assert!(min.is_normal());
                    /// assert!(max.is_normal());
                    ///
                    /// assert!(!zero.is_normal());
                    /// assert!(!f64::NAN.is_normal());
                    /// assert!(!f64::INFINITY.is_normal());
                    /// // Values between `0` and `min` are Subnormal.
                    /// assert!(!lower_than_min.is_normal());
                    /// ```
                    /// [subnormal]: https://en.wikipedia.org/wiki/Denormal_number
                    #[doc(alias = "isNormal")]
                    #[must_use]
                    pub fn is_normal { isNormal }
                );

                /// IEEE 754 5.7.2 **class**
                #[must_use]
                #[inline]
                pub fn class(self) -> Class {
                    // SAFETY: Return value of __bid $x _class is a valid class
                    unsafe { core::mem::transmute([<__bid $x _class>](self.inner)) }
                }

                /// Returns the floating point category of the number. If only one property
                /// is going to be tested, it is generally faster to use the specific
                /// predicate instead.
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                /// use core::num::FpCategory;
                ///
                #[doc = "let num = d" $x "!(12.4);"]
                #[doc = "let inf = Decimal" $x "::INFINITY;"]
                ///
                /// assert_eq!(num.classify(), FpCategory::Normal);
                /// assert_eq!(inf.classify(), FpCategory::Infinite);
                /// ```
                #[must_use]
                #[inline]
                pub fn classify(self) -> FpCategory {
                    self.class().into()
                }

                /// Returns `true` if `self` has a positive sign, including `+0.0`, `NaN`s with
                /// positive sign bit and positive infinity.
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let d = d" $x "!(7.0);"]
                #[doc = "let g = d" $x "!(-7.0);"]
                #[doc = "let nan = Decimal" $x "::NAN;"]
                #[doc = "let neg_nan = Decimal" $x "::NEG_NAN;"]
                ///
                /// assert!(d.is_sign_positive());
                /// assert!(!g.is_sign_positive());
                /// assert!(nan.is_sign_positive());
                /// assert!(!neg_nan.is_sign_positive());
                /// ```
                #[must_use]
                #[inline]
                pub const fn is_sign_positive(self) -> bool {
                    !self.is_sign_negative()
                }

                /// Returns `true` if `self` has a negative sign, including `-0.0`, `NaN`s with
                /// negative sign bit and negative infinity.
                ///
                /// IEEE 754 5.7.2 **isSignMinus**
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let d = d" $x "!(7.0);"]
                #[doc = "let g = d" $x "!(-7.0);"]
                #[doc = "let nan = Decimal" $x "::NAN;"]
                #[doc = "let neg_nan = Decimal" $x "::NEG_NAN;"]
                ///
                /// assert!(!d.is_sign_negative());
                /// assert!(g.is_sign_negative());
                /// assert!(!nan.is_sign_negative());
                /// assert!(neg_nan.is_sign_negative());
                /// ```
                #[doc(alias = "isSignMinus")]
                #[must_use]
                #[inline]
                pub const fn is_sign_negative(self) -> bool {
                    const SIGN_MASK: [<u$x>] = 1 << ($x - 1);
                    (self.to_bits() & SIGN_MASK) == SIGN_MASK
                }

                /// Returns `true` if this value is a signaling `NaN`.
                ///
                /// IEEE 754 5.7.2 **isSignaling**
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let nan = Decimal" $x "::NAN;"]
                #[doc = "let snan = Decimal" $x "::SNAN;"]
                #[doc = "let d = d" $x "!(7.0);"]
                ///
                /// assert!(!nan.is_signaling());
                /// assert!(snan.is_signaling());
                /// assert!(!d.is_signaling());
                /// ```
                #[doc(alias = "isSignaling")]
                #[must_use]
                #[inline]
                pub const fn is_signaling(self) -> bool {
                    const SIGNALING_MASK: [<u$x>] = 0x7e << ($x - 8);
                    (self.to_bits() & SIGNALING_MASK) == SIGNALING_MASK
                }

                decimal_op_simple_bool!($x,
                    /// IEEE 754 5.7.2 **isCanonical**
                    #[doc(alias = "isCanonical")]
                    #[must_use]
                    pub fn is_canonical { isCanonical }
                );

                /// Takes the reciprocal (inverse) of a number, `1/x`.
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let x = d" $x "!(2.0);"]
                #[doc = "let abs_difference = (x.recip() - ( d" $x "!(1.0) / x)).abs();"]
                ///
                #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                /// ```
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn recip(self) -> Self {
                    [<d$x>]!(1) / self
                }

                // FIXME use 64 * 128 -> 64
                /// Converts radians to degrees.
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let angle = decimalfp::decimal" $x "::consts::PI;"]
                ///
                #[doc = "let abs_difference = (angle.to_degrees() - d" $x "!(180.0)).abs();"]
                ///
                #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                /// ```
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn to_degrees(self) -> Self {
                    only_32!($x, let ret = self * [<decimal$x>]::consts::FRAC_180_PI;);
                    only_64_128!($x, let ret = Context::default().mul(self, decimal128::consts::FRAC_180_PI););
                    ret
                }

                // FIXME use 64 * 128 -> 64
                /// Converts degrees to radians.
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let angle = d" $x "!(180.0);"]
                ///
                #[doc = "let abs_difference = (angle.to_radians() - decimalfp::decimal" $x "::consts::PI).abs();"]
                ///
                #[doc = "assert!(abs_difference <= Decimal" $x "::EPSILON);"]
                /// ```
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn to_radians(self) -> Self {
                    only_32!($x, let ret = self * [<decimal$x>]::consts::FRAC_PI_180;);
                    only_64_128!($x, let ret = Context::default().mul(self, decimal128::consts::FRAC_PI_180););
                    ret
                }

                decimal_op_forward!(
                    /// Returns the maximum of the two numbers.
                    ///
                    /// Follows the IEEE-754 2008 semantics for maxNum.
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(1.0);"]
                    #[doc = "let y = d" $x "!(2.0);"]
                    ///
                    /// assert_eq!(x.max(y), y);
                    #[doc = "assert_eq!(x.max(Decimal" $x "::NAN), x);"]
                    /// ```
                    ///
                    /// If one of the arguments is NaN, then the other argument is returned.
                    #[doc(alias = "maxNum")]
                    #[must_use = "this returns the result of the comparison, without modifying either input"]
                    pub fn max(self, other: Self) -> Self
                );

                decimal_op_forward!(
                    /// Returns the minimum of the two numbers.
                    ///
                    /// Follows the IEEE-754 2008 semantics for minNum.
                    ///
                    /// ```
                    /// use decimalfp::prelude::*;
                    ///
                    #[doc = "let x = d" $x "!(1.0);"]
                    #[doc = "let y = d" $x "!(2.0);"]
                    ///
                    /// assert_eq!(x.min(y), x);
                    #[doc = "assert_eq!(x.min(Decimal" $x "::NAN), x);"]
                    /// ```
                    ///
                    /// If one of the arguments is NaN, then the other argument is returned.
                    #[doc(alias = "minNum")]
                    #[must_use = "this returns the result of the comparison, without modifying either input"]
                    pub fn min(self, other: Self) -> Self
                );

                // FIXME minimum maximum

                /// Converts the given integer to a decimal,
                /// with round-to-even rounding,
                /// saturating to infinity if it doesn't fit.
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn from_int<Int>(int: Int) -> Self
                where
                    Self: convert::DecimalFromInt<Int>,
                    Int: private::Sealed,
                {
                    Context::new().from_int(int)
                }

                /// Rounds toward zero and converts to any primitive integer type,
                /// saturating if the value does not fit in that type,
                /// and returning `0` if it is `NaN`.
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let value = d" $x "!(4.6);"]
                /// let rounded = value.to_int::<u16>();
                /// assert_eq!(rounded, 4);
                ///
                #[doc = "let value = d" $x "!(-128.9);"]
                /// let rounded = value.to_int::<i8>();
                /// assert_eq!(rounded, i8::MIN);
                ///
                #[doc = "let value = d" $x "!(-129.0);"]
                /// let rounded = value.to_int::<i8>();
                /// assert_eq!(rounded, i8::MIN);
                ///
                #[doc = "let value = Decimal" $x "::NAN;"]
                /// let rounded = value.to_int::<i8>();
                /// assert_eq!(rounded, 0);
                /// ```
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn to_int<Int>(self) -> Int
                where
                    Self: convert::DecimalToInt<Int>,
                    Int: private::Sealed,
                {
                    self.to_int_checked().unwrap_or_else(|| {
                        if self.is_nan() {
                            <Self as convert::DecimalToInt<Int>>::INT_ZERO
                        } else if self.is_sign_positive() {
                            <Self as convert::DecimalToInt<Int>>::INT_MAX
                        } else {
                            <Self as convert::DecimalToInt<Int>>::INT_MIN
                        }
                    })
                }

                /// Rounds toward zero and converts to any primitive integer type,
                /// returning `None` if the value is not finite or does not fit in that type.
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let value = d" $x "!(4.6);"]
                /// let rounded = value.to_int_checked::<u16>();
                /// assert_eq!(rounded, Some(4));
                ///
                #[doc = "let value = d" $x "!(-128.9);"]
                /// let rounded = value.to_int_checked::<i8>();
                /// assert_eq!(rounded, Some(i8::MIN));
                ///
                #[doc = "let value = d" $x "!(-129.0);"]
                /// let rounded = value.to_int_checked::<i8>();
                /// assert_eq!(rounded, None);
                /// ```
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn to_int_checked<Int>(self) -> Option<Int>
                where
                    Self: convert::DecimalToInt<Int>,
                    Int: private::Sealed,
                {
                    let mut ctx = Context::new();

                    let result = ctx.to_int_trunc(self);

                    // IEEE 754 5.8
                    if ctx.flags.contains(Flags::INVALID_OPERATION) {
                        None
                    } else {
                        Some(result)
                    }
                }


                /// Rounds toward zero and converts to any primitive integer type,
                /// assuming that the value is finite and fits in that type.
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "let value = d" $x "!(4.6);"]
                /// let rounded = unsafe { value.to_int_unchecked::<u16>() };
                /// assert_eq!(rounded, 4);
                ///
                #[doc = "let value = d" $x "!(-128.9);"]
                /// let rounded = unsafe { value.to_int_unchecked::<i8>() };
                /// assert_eq!(rounded, i8::MIN);
                /// ```
                ///
                /// # Safety
                ///
                /// The value must:
                ///
                /// * Not be `NaN`
                /// * Not be infinite
                /// * Be representable in the return type `Int`, after truncating off its fractional part
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub unsafe fn to_int_unchecked<Int>(self) -> Int
                where
                    Self: convert::DecimalToInt<Int>,
                    Int: private::Sealed,
                {
                    unsafe { self.to_int_checked().unwrap_unchecked() }
                }

                /// Convert the given decimal into this type.
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn convert_from<Src>(src: Src) -> Self
                where
                    Self: convert::DecimalConvertFormat<Src>,
                    Src: private::Sealed,
                {
                    Context::new().convert_format(src)
                }


                /// Convert this decimal into the given type.
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn convert_into<Dest>(self) -> Dest
                where
                    Dest: convert::DecimalConvertFormat<Self>
                {
                    Context::new().convert_format(self)
                }

                // FIXME to/from bits doctests

                /// Raw transmutation to
                #[doc = "`u" $x "`."]
                /// Uses the IEEE 754 binary encoding for decimal floats.
                ///
                /// This is identical to
                #[doc = "`transmute::<Decimal" $x ", u" $x "`."]
                ///
                /// Note that this function is distinct from `to_int` conversion, which attempts to
                /// preserve the *numeric* value, and not the bitwise value.
                ///
                /// IEEE 754 5.5.2 **encodeBinary**
                #[doc(alias = "encodeBinary")]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub const fn to_bits(self) -> [<u$x>] {
                    // SAFETY: `Decimal$x` is a plain old datatype so we can always transmute  it
                    unsafe { core::mem::transmute(self) }
                }

                /// Raw transmutation from
                #[doc = "`u" $x "`."]
                /// Uses the IEEE 754 binary encoding for decimal floats.
                ///
                /// This is identical to
                #[doc = "`transmute::<u" $x ", Decimal" $x "`."]
                ///
                /// Note that this function is distinct from `from_int` conversion, which attempts to
                /// preserve the *numeric* value, and not the bitwise value.
                ///
                /// IEEE 754 5.5.2 **decodeBinary**
                #[doc(alias = "decodeBinary")]
                #[must_use]
                #[inline]
                pub const fn from_bits(v: [<u$x>]) -> Self {
                    // SAFETY: `Decimal$x` is a plain old datatype so we can always transmute to it.
                    unsafe { core::mem::transmute(v) }
                }

                /// Return the memory representation of this floating point number as a byte array in
                /// big-endian (network) byte order.
                /// Uses the IEEE 754 binary encoding for decimal floats.
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub const fn to_be_bytes(self) -> [u8; $x / 8] {
                    self.to_bits().to_be_bytes()
                }

                /// Return the memory representation of this floating point number as a byte array in
                /// little-endian byte order.
                /// Uses the IEEE 754 binary encoding for decimal floats.
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub const fn to_le_bytes(self) -> [u8; $x / 8] {
                    self.to_bits().to_le_bytes()
                }

                /// Return the memory representation of this floating point number as a byte array in
                /// native byte order.
                ///
                /// Uses the IEEE 754 binary encoding for decimal floats.
                ///
                /// As the target platform's native endianness is used, portable code
                /// should use [`to_be_bytes`] or [`to_le_bytes`], as appropriate, instead.
                ///
                /// [`to_be_bytes`]:
                #[doc = "Decimal" $x "::to_be_bytes"]
                /// [`to_le_bytes`]:
                #[doc = "Decimal" $x "::to_le_bytes"]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub const fn to_ne_bytes(self) -> [u8; $x / 8] {
                    self.to_bits().to_ne_bytes()
                }

                /// Create a floating point value from its representation as a byte array in big endian.
                ///
                /// Uses the IEEE 754 binary encoding for decimal floats.
                #[must_use]
                #[inline]
                pub const fn from_be_bytes(bytes: [u8; $x / 8]) -> Self {
                    Self::from_bits([<u$x>]::from_be_bytes(bytes))
                }

                /// Create a floating point value from its representation as a byte array in little endian.
                ///
                /// Uses the IEEE 754 binary encoding for decimal floats.
                #[must_use]
                #[inline]
                pub const fn from_le_bytes(bytes: [u8; $x / 8]) -> Self {
                    Self::from_bits([<u$x>]::from_le_bytes(bytes))
                }

                /// Create a floating point value from its representation as a byte array in native endian.
                ///
                /// Uses the IEEE 754 binary encoding for decimal floats.
                ///
                /// As the target platform's native endianness is used, portable code
                /// likely wants to use [`from_be_bytes`] or [`from_le_bytes`], as
                /// appropriate instead.
                ///
                /// [`from_be_bytes`]:
                #[doc = "Decimal" $x "::from_be_bytes"]
                /// [`from_le_bytes`]:
                #[doc = "Decimal" $x "::from_le_bytes"]
                #[must_use]
                #[inline]
                pub const fn from_ne_bytes(bytes: [u8; $x / 8]) -> Self {
                    Self::from_bits([<u$x>]::from_ne_bytes(bytes))
                }

                /// Raw transmutation to
                #[doc = "`u" $x "`,"]
                /// in the IEEE 754 decimal encoding.
                ///
                /// IEEE 754 5.5.2 **encodeDecimal**
                #[doc(alias = "encodeDecimal")]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                #[allow(clippy::useless_transmute)]
                pub fn to_bits_decimal_encoding(self) -> [<u$x>] {
                    // SAFETY: `Decimal$x` is a plain old datatype so we can always transmute  it
                    unsafe { core::mem::transmute([<__bid_to_dpd$x>](self.inner)) }
                }

                /// Raw transmutation from
                #[doc = "`u" $x "`."]
                /// in the IEEE 754 decimal encoding.
                ///
                /// IEEE 754 5.5.2 **decodeDecimal**
                #[doc(alias = "decodeDecimal")]
                #[must_use]
                #[inline]
                #[allow(clippy::useless_transmute)]
                pub fn from_bits_decimal_encoding(v: [<u$x>]) -> Self {
                    // SAFETY: `Decimal$x` is a plain old datatype so we can always transmute to it.
                    Self { inner: unsafe { [<__bid_dpd_to_bid$x>](core::mem::transmute(v)) } }

                }

                /// Return the IEEE 754 decimal encoding representation of this floating point number as a byte array in
                /// big-endian (network) byte order.
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn to_be_bytes_decimal_encoding(self) -> [u8; $x / 8] {
                    self.to_bits_decimal_encoding().to_be_bytes()
                }

                /// Return the IEEE 754 decimal encoding representation of this floating point number as a byte array in
                /// little-endian byte order.
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn to_le_bytes_decimal_encoding(self) -> [u8; $x / 8] {
                    self.to_bits_decimal_encoding().to_le_bytes()
                }

                /// Return the IEEE 754 decimal encoding representation of this floating point number as a byte array in
                /// native byte order.
                ///
                /// As the target platform's native endianness is used, portable code
                /// should use [`to_be_bytes_decimal_encoding`] or [`to_le_bytes_decimal_encoding`], as appropriate, instead.
                ///
                /// [`to_be_bytes_decimal_encoding`]:
                #[doc = "Decimal" $x "::to_be_bytes_decimal_encoding"]
                /// [`to_le_bytes_decimal_encoding`]:
                #[doc = "Decimal" $x "::to_le_bytes_decimal_encoding"]
                #[must_use = "this returns the result of the operation, without modifying the original"]
                #[inline]
                pub fn to_ne_bytes_decimal_encoding(self) -> [u8; $x / 8] {
                    self.to_bits_decimal_encoding().to_ne_bytes()
                }

                /// Create a floating point value from its representation as a IEEE 754 decimal encoding byte array in big endian.
                #[must_use]
                #[inline]
                pub fn from_be_bytes_decimal_encoding(bytes: [u8; $x / 8]) -> Self {
                    Self::from_bits_decimal_encoding([<u$x>]::from_be_bytes(bytes))
                }

                /// Create a floating point value from its representation as a IEEE 754 decimal encoding byte array in little endian.
                #[must_use]
                #[inline]
                pub fn from_le_bytes_decimal_encoding(bytes: [u8; $x / 8]) -> Self {
                    Self::from_bits_decimal_encoding([<u$x>]::from_le_bytes(bytes))
                }

                /// Create a floating point value from its representation as a IEEE 754 decimal encoding byte array in native endian.
                ///
                /// As the target platform's native endianness is used, portable code
                /// likely wants to use [`from_be_bytes_decimal_encoding`] or [`from_le_bytes_decimal_encoding`], as
                /// appropriate instead.
                ///
                /// [`from_be_bytes_decimal_encoding`]:
                #[doc = "Decimal" $x "::from_be_bytes_decimal_encoding"]
                /// [`from_le_bytes_decimal_encoding`]:
                #[doc = "Decimal" $x "::from_le_bytes_decimal_encoding"]
                #[must_use]
                #[inline]
                pub fn from_ne_bytes_decimal_encoding(bytes: [u8; $x / 8]) -> Self {
                    Self::from_bits_decimal_encoding([<u$x>]::from_ne_bytes(bytes))
                }

                decimal_op_simple_bool!($x,
                    /// IEEE 754 5.7.2 **totalOrder**
                    #[doc(alias = "totalOrder")]
                    #[must_use]
                    pub fn total_order(other) { totalOrder } // FIXME rename?
                );

                decimal_op_simple_bool!($x,
                    /// IEEE 754 5.7.2 **totalOrderMag**
                    #[doc(alias = "totalOrderMag")]
                    #[must_use]
                    pub fn total_order_mag(other) { totalOrderMag }
                );

                /// Returns an ordering between self and other values.
                /// Unlike the standard partial comparison between floating point numbers,
                /// this comparison always produces an ordering in accordance to
                /// the totalOrder predicate as defined in IEEE 754 (2008 revision)
                /// floating point standard. The values are ordered in following order:
                /// - Negative quiet NaN
                /// - Negative signaling NaN
                /// - Negative infinity
                /// - Negative numbers
                /// - Negative subnormal numbers
                /// - Negative zero
                /// - Positive zero
                /// - Positive subnormal numbers
                /// - Positive numbers
                /// - Positive infinity
                /// - Positive signaling NaN
                /// - Positive quiet NaN
                ///
                /// Note that this function does not always agree with the [`PartialOrd`]
                /// and [`PartialEq`] implementations of
                #[doc = "`Decimal" $x "`."]
                /// In particular, they regard
                /// negative and positive zero as equal, while `total_cmp` doesn't.
                ///
                /// # Example
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                /// struct GoodBoy {
                ///     name: String,
                #[doc = "weight: Decimal" $x ","]
                /// }
                ///
                /// let mut bois = vec![
                #[doc = "    GoodBoy { name: \"Pucci\".to_owned(), weight: d" $x "!(0.1) },"]
                #[doc = "    GoodBoy { name: \"Woofer\".to_owned(), weight: d" $x "!(99.0) },"]
                #[doc = "    GoodBoy { name: \"Yapper\".to_owned(), weight: d" $x "!(10.0) },"]
                #[doc = "    GoodBoy { name: \"Chonk\".to_owned(), weight: Decimal" $x "::INFINITY },"]
                #[doc = "    GoodBoy { name: \"Abs. Unit\".to_owned(), weight: Decimal" $x "::NAN },"]
                #[doc = "    GoodBoy { name: \"Floaty\".to_owned(), weight: d" $x "!(-5.0)},"]
                /// ];
                ///
                /// bois.sort_by(|a, b| a.weight.total_cmp(&b.weight));
                /// # assert!(bois.into_iter().map(|b| b.weight)
                #[doc = "#     .zip([d" $x "!(-5.0), d" $x "!(0.1), d" $x "!(10.0), d" $x "!(99.0), Decimal" $x "::INFINITY, Decimal" $x "::NAN].iter())"]
                /// #     .all(|(a, b)| a.to_bits() == b.to_bits()))
                /// ```
                #[must_use]
                #[inline]
                pub fn total_cmp(&self, other: &Self) -> Ordering {
                    match (self.total_order(*other), other.total_order(*self)) {
                        (true, false) => Ordering::Less,
                        (true, true) => Ordering::Equal,
                        (false, true) => Ordering::Greater,
                        // SAFETY: Total order is total, either a <= b or b >= a
                        (false, false) => unsafe { core::hint::unreachable_unchecked() }
                    }
                }

                decimal_op_simple_bool!($x,
                    /// IEEE 754 5.7.3 **sameQuantum**
                    #[doc(alias = "sameQuantum")]
                    #[must_use]
                    pub fn same_quantum(other) { sameQuantum }
                );

                /// Restrict a value to a certain interval unless it is NaN.
                ///
                /// Returns `max` if `self` is greater than `max`, and `min` if `self` is
                /// less than `min`. Otherwise this returns `self`.
                ///
                /// Note that this function returns NaN if the initial value was NaN as
                /// well.
                ///
                /// # Panics
                ///
                /// Panics if `min > max`, `min` is NaN, or `max` is NaN.
                ///
                /// # Examples
                ///
                /// ```
                /// use decimalfp::prelude::*;
                ///
                #[doc = "assert!(d" $x "!(-3.0).clamp(d" $x "!(-2.0), d" $x "!(1.0)) == d" $x "!(-2.0));"]
                #[doc = "assert!(d" $x "!(0.0).clamp(d" $x "!(-2.0), d" $x "!(1.0)) == d" $x "!(0.0));"]
                #[doc = "assert!(d" $x "!(2.0).clamp(d" $x "!(-2.0), d" $x "!(1.0)) == d" $x "!(1.0));"]
                #[doc = "assert!(Decimal" $x "::NAN.clamp(d" $x "!(-2.0), d" $x "!(1.0)).is_nan());"]
                /// ```
                #[must_use = "method returns a new number and does not mutate the original value"]
                #[inline]
                pub fn clamp(self, min: Self, max: Self) -> Self {
                    // FIXME: clamp -0 to +0?
                    assert!(min <= max);
                    let mut x = self;
                    if x < min {
                        x = min;
                    }
                    if x > max {
                        x = max;
                    }
                    x
                }

                // TODO make private
                /// Returns the significand, base 10 exponent, and signedness, in that order.
                /// The original number can be recovered by (if sign { -1 } else { 1 }) * significand * 10 ^ exponent.
                /// Result is not specified for NaN/infinity.
                #[must_use]
                #[inline]
                pub fn integer_decode(self) -> ([<u$x>], i16, bool) {
                    // IEEE 3.5.2

                    // IEEE table 3.6
                    const EMAX: i32  = [<Decimal$x>]::MAX_EXP - 1;
                    const BIAS: i32  = (EMAX + ([<Decimal$x>]::DIGITS as i32) - 2);
                    const W_PLUS_5: u32 = $x / 16 + 9;
                    const T: u32 = 15 * $x / 16 - 10;
                    const J: u32 = T / 10;
                    const MAX_SIGNIFICAND: [<u$x>] = (10 as [<u$x>]).pow(3 * J + 1) - 1;

                    let bits: [<u$x>] = self.to_bits();

                    let signed: bool = bits >> ($x - 1) == 1;
                    let combination: u32 = ((bits << 1) >> ($x - W_PLUS_5)) as u32;
                    let trailing: [<u$x>] = (bits << ($x - T)) >> ($x - T);

                    let case_i: bool = (combination >> (W_PLUS_5 - 2)) != 0b11;

                    let biased_exponent: i32;
                    let mut significand: [<u$x>];
                    if case_i {
                        biased_exponent = (combination >> 3) as i32;
                        significand = trailing + (((combination & 0b111) as [<u$x>]) << T);
                    } else {
                        biased_exponent = ((combination ^ (0b11 << (W_PLUS_5 - 2))) >> 1) as i32;
                        significand  = trailing + (((8 + (combination & 0b1)) as [<u$x>]) << T);
                    }

                    // non-canonical significand
                    if significand > MAX_SIGNIFICAND {
                        significand = 0;
                    }

                    let exponent = (biased_exponent - BIAS) as i16;

                    return (significand, exponent, signed)
                }
            }

            impl Default for [<Decimal$x>] {
                fn default() -> Self {
                    [<d$x>]!(0)
                }
            }

            decimal_binop_trait!(impl Rem, rem, RemAssign for $x);

            decimal_binop_trait!(impl Add, add, AddAssign for $x);

            decimal_binop_trait!(impl Sub, sub, SubAssign for $x);

            decimal_binop_trait!(impl Mul, mul, MulAssign for $x);

            decimal_binop_trait!(impl Div, div, DivAssign for $x);

            impl Neg for [<Decimal$x>] {
                type Output = Self;

                /// IEEE 754 5.5.1 **negate**
                #[doc(alias = "negate")]
                #[inline]
                fn neg(self) -> Self {
                    const SIGN_MASK: [<u$x>] = 1 << ($x - 1);
                    Self::from_bits(self.to_bits() ^ SIGN_MASK)
                }
            }

            forward_ref_unop!(impl Neg, neg for [<Decimal$x>]);

            impl Sum<[<Decimal$x>]> for [<Decimal$x>] {
                fn sum<I: Iterator<Item=Self>>(iter: I) -> Self {
                    iter.fold(
                        [<d$x>]!(0),
                        |a, b| a + b,
                    )
                }
            }

            impl<'a> Sum<&'a [<Decimal$x>]> for [<Decimal$x>] {
                fn sum<I: Iterator<Item=&'a Self>>(iter: I) -> Self {
                    iter.fold(
                        [<d$x>]!(0),
                        |a, b| a + b,
                    )
                }
            }

            impl Product<[<Decimal$x>]> for [<Decimal$x>] {
                fn product<I: Iterator<Item=Self>>(iter: I) -> Self {
                    iter.fold(
                        [<d$x>]!(1),
                        |a, b| a * b,
                    )
                }
            }

            impl<'a> Product<&'a [<Decimal$x>]> for [<Decimal$x>] {
                fn product<I: Iterator<Item=&'a Self>>(iter: I) -> Self {
                    iter.fold(
                        [<d$x>]!(1),
                        |a, b| a * b,
                    )
                }
            }

            impl PartialEq for [<Decimal$x>] {
                #[inline]
                fn eq(&self, other: &[<Decimal$x>]) -> bool {
                    Context::new().eq(*self, *other)
                }

                #[inline]
                #[allow(clippy::partialeq_ne_impl)]
                fn ne(&self, other: &[<Decimal$x>]) -> bool {
                    Context::new().ne(*self, *other)
                }
            }

            impl PartialOrd for [<Decimal$x>] {
                fn partial_cmp(&self, other: &[<Decimal$x>]) -> Option<Ordering> {
                    match (self <= other, self >= other) {
                        (false, false) => None,
                        (false, true) => Some(Ordering::Greater),
                        (true, false) => Some(Ordering::Less),
                        (true, true) => Some(Ordering::Equal),
                    }
                }

                #[inline]
                fn lt(&self, other: &[<Decimal$x>]) -> bool {
                    Context::new().lt(*self, *other)
                }

                #[inline]
                fn le(&self, other: &[<Decimal$x>]) -> bool {
                    Context::new().le(*self, *other)
                }

                #[inline]
                fn gt(&self, other: &[<Decimal$x>]) -> bool {
                    Context::new().gt(*self, *other)
                }

                #[inline]
                fn ge(&self, other: &[<Decimal$x>]) -> bool {
                    Context::new().ge(*self, *other)
                }
            }

            impl FromStr for [<Decimal$x>] {
                type Err = Infallible;

                #[inline]
                fn from_str(s: &str) -> Result<Self, Self::Err> {
                    // FIXME let else
                    return Ok(if let Ok(c_str) = CString::new(s) {
                        let dec = Context::new().from_c_str(&c_str);
                        dec
                    } else {
                        Self::NAN
                    })
                }
            }

            impl fmt::Debug for [<Decimal$x>] {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
                    let str = Context::new().to_string(*self);
                    write!(f, "{}", str)
                }
            }

            impl fmt::Display for [<Decimal$x>] {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
                    let str = Context::new().to_string(*self);
                    write!(f, "{}", str)
                }
            }

            impl fmt::LowerExp for [<Decimal$x>] {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
                    let str = Context::new().to_string(*self).to_lowercase();
                    write!(f, "{}", str)
                }
            }

            impl fmt::UpperExp for [<Decimal$x>] {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
                    let str = Context::new().to_string(*self);
                    write!(f, "{}", str)
                }
            }

            decimal_from_int_impl!($x, i8, u8, i16, u16);

            only_64_128!($x,
                decimal_from_int_impl!($x, i32, u32);

                from_convert_format_impl!([<Decimal$x>], Decimal32);
            );

            only_128!($x,
                decimal_from_int_impl!($x, i64, u64);

                from_convert_format_impl!([<Decimal$x>], Decimal64);

                // f16 has a maximum of 21 decimal digits. bf16 can have way more
                #[cfg(feature = "half")]
                from_convert_format_impl!([<Decimal$x>], half::f16);
            );

            #[cfg(feature = "alga")]
            const _: () = {
                use alga::general::{Additive, Multiplicative};

                impl alga::general::AbstractField for [<Decimal$x>] {}
                impl alga::general::AbstractGroup<Additive> for [<Decimal$x>] {}
                impl alga::general::AbstractGroup<Multiplicative> for [<Decimal$x>] {}
                impl alga::general::AbstractGroupAbelian<Additive> for [<Decimal$x>] {}
                impl alga::general::AbstractGroupAbelian<Multiplicative> for [<Decimal$x>] {}
                impl alga::general::AbstractLoop<Additive> for [<Decimal$x>] {}
                impl alga::general::AbstractLoop<Multiplicative> for [<Decimal$x>] {}

                impl alga::general::AbstractMagma<Additive> for [<Decimal$x>] {
                    #[inline]
                    fn operate(&self, right: &Self) -> Self {
                        *self + *right
                    }
                }

                impl alga::general::AbstractMagma<Multiplicative> for [<Decimal$x>] {
                    #[inline]
                    fn operate(&self, right: &Self) -> Self {
                        *self * *right
                    }
                }

                impl alga::general::AbstractModule for [<Decimal$x>] {
                    type AbstractRing = Self;

                    #[inline]
                    fn multiply_by(&self, r: Self) -> Self {
                        self.clone() * r
                    }
                }

                impl alga::general::AbstractMonoid<Additive> for [<Decimal$x>] {}
                impl alga::general::AbstractMonoid<Multiplicative> for [<Decimal$x>] {}
                impl alga::general::AbstractQuasigroup<Additive> for [<Decimal$x>] {}
                impl alga::general::AbstractQuasigroup<Multiplicative> for [<Decimal$x>] {}
                impl alga::general::AbstractRing for [<Decimal$x>] {}
                impl alga::general::AbstractRingCommutative for [<Decimal$x>] {}
                impl alga::general::AbstractSemigroup<Additive> for [<Decimal$x>] {}
                impl alga::general::AbstractSemigroup<Multiplicative> for [<Decimal$x>] {}

                impl alga::general::ComplexField for [<Decimal$x>] {
                    type RealField = Self;

                    #[inline]
                    fn from_real(re: Self::RealField) -> Self {
                        re
                    }

                    #[inline]
                    fn real(self) -> Self::RealField {
                        self
                    }

                    #[inline]
                    fn imaginary(self) -> Self::RealField {
                        [<d$x>]!(0)
                    }

                    #[inline]
                    fn norm1(self) -> Self::RealField {
                        self.abs()
                    }

                    #[inline]
                    fn modulus(self) -> Self::RealField {
                        self.abs()
                    }

                    #[inline]
                    fn modulus_squared(self) -> Self::RealField {
                        self * self
                    }

                    #[inline]
                    fn argument(self) -> Self::RealField {
                        if self >= [<d$x>]!(0) {
                            [<d$x>]!(0)
                        } else {
                            [<decimal$x>]::consts::PI
                        }
                    }

                    #[inline]
                    fn to_exp(self) -> (Self, Self) {
                        if self >= [<d$x>]!(0) {
                            (self, [<d$x>]!(1))
                        } else {
                            (-self, [<d$x>]!(-1))
                        }
                    }

                    trait_forward!($x, recip(self) -> Self);

                    #[inline]
                    fn conjugate(self) -> Self {
                        self
                    }

                    #[inline]
                    fn scale(self, factor: Self::RealField) -> Self {
                        self * factor
                    }

                    #[inline]
                    fn unscale(self, factor: Self::RealField) -> Self {
                        self / factor
                    }

                    trait_forward!($x, floor(self) -> Self);
                    trait_forward!($x, ceil(self) -> Self);
                    trait_forward!($x, round(self) -> Self);
                    trait_forward!($x, trunc(self) -> Self);
                    trait_forward!($x, fract(self) -> Self);
                    trait_forward!($x, abs(self) -> Self);
                    trait_forward!($x, signum(self) -> Self);
                    trait_forward!($x, mul_add(self, a: Self, b: Self) -> Self);
                    trait_forward!($x, powi(self, n: i32) -> Self);
                    trait_forward!($x, powf(self, n: Self) -> Self);
                    #[inline]
                    fn powc(self, n: Self) -> Self {
                        self.powf(n)
                    }
                    trait_forward!($x, sqrt(self) -> Self);

                    #[inline]
                    fn try_sqrt(self) -> Option<Self> {
                        if self >= [<d$x>]!(0) {
                            Some(self.sqrt())
                        } else {
                            None
                        }
                    }

                    trait_forward!($x, exp(self) -> Self);
                    trait_forward!($x, exp2(self) -> Self);
                    trait_forward!($x, exp_m1(self) -> Self);
                    trait_forward!($x, ln_1p(self) -> Self);
                    trait_forward!($x, ln(self) -> Self);
                    trait_forward!($x, log(self, base: Self) -> Self);
                    trait_forward!($x, log2(self) -> Self);
                    trait_forward!($x, log10(self) -> Self);
                    trait_forward!($x, cbrt(self) -> Self);
                    trait_forward!($x, hypot(self, other: Self) -> Self);
                    trait_forward!($x, sin(self) -> Self);
                    trait_forward!($x, cos(self) -> Self);
                    trait_forward!($x, tan(self) -> Self);
                    trait_forward!($x, asin(self) -> Self);
                    trait_forward!($x, acos(self) -> Self);
                    trait_forward!($x, atan(self) -> Self);
                    trait_forward!($x, sin_cos(self) -> (Self, Self));
                    trait_forward!($x, sinh(self) -> Self);
                    trait_forward!($x, cosh(self) -> Self);
                    trait_forward!($x, tanh(self) -> Self);
                    trait_forward!($x, asinh(self) -> Self);
                    trait_forward!($x, acosh(self) -> Self);
                    trait_forward!($x, atanh(self) -> Self);

                    #[inline]
                    fn is_finite(&self) -> bool {
                        [<Decimal$x>]::is_finite(*self)
                    }
                }

                impl alga::general::Identity<Additive> for [<Decimal$x>] {
                    #[inline]
                    fn identity() -> Self {
                        [<d$x>]!(0)
                    }
                }

                impl alga::general::Identity<Multiplicative> for [<Decimal$x>] {
                    #[inline]
                    fn identity() -> Self {
                        [<d$x>]!(1)
                    }
                }

                impl alga::general::JoinSemilattice for [<Decimal$x>] {
                    #[inline]
                    fn join(&self, other: &Self) -> Self {
                        if *self >= *other {
                            *self
                        }
                        else {
                            *other
                        }
                    }
                }

                impl alga::general::Lattice for [<Decimal$x>] {
                    #[inline]
                    fn meet_join(&self, other: &Self) -> (Self, Self) {
                        if *self >= *other {
                            (*other, *self)
                        }
                        else {
                            (*self, *other)
                        }
                    }
                }

                impl alga::general::MeetSemilattice for [<Decimal$x>] {
                    #[inline]
                    fn meet(&self, other: &Self) -> Self {
                        if *self <= *other {
                            *self
                        }
                        else {
                            *other
                        }
                    }
                }

                impl alga::general::Module for [<Decimal$x>] {
                    type Ring = [<Decimal$x>];
                }

                impl alga::general::RealField for [<Decimal$x>] {
                    trait_forward!($x, is_sign_positive(self) -> bool);
                    trait_forward!($x, is_sign_negative(self) -> bool);
                    trait_forward!($x, max(self, other: Self) -> Self);
                    trait_forward!($x, min(self, other: Self) -> Self);
                    trait_forward!($x, atan2(self, other: Self) -> Self);
                    trait_forward_const_math!($x, pi { PI });
                    trait_forward_const_math!($x, frac_pi_2 { FRAC_PI_2 });
                    trait_forward_const_math!($x, frac_pi_3 { FRAC_PI_3 });
                    trait_forward_const_math!($x, frac_pi_4 { FRAC_PI_4 });
                    trait_forward_const_math!($x, frac_pi_6 { FRAC_PI_6 });
                    trait_forward_const_math!($x, frac_pi_8 { FRAC_PI_8 });
                    trait_forward_const_math!($x, frac_1_pi { FRAC_1_PI });
                    trait_forward_const_math!($x, frac_2_pi { FRAC_2_PI });
                    trait_forward_const_math!($x, frac_2_sqrt_pi { FRAC_2_SQRT_PI });
                    trait_forward_const_math!($x, e { E });
                    trait_forward_const_math!($x, log2_e { LOG2_E });
                    trait_forward_const_math!($x, log10_e { LOG10_E });
                    trait_forward_const_math!($x, ln_2 { LN_2 });
                    trait_forward_const_math!($x, ln_10 { LN_10 });

                    #[inline]
                    fn two_pi() -> Self {
                        [<decimal$x>]::consts::TAU
                    }
                }

                impl alga::general::TwoSidedInverse<Additive> for [<Decimal$x>] {
                    #[inline]
                    fn two_sided_inverse(&self) -> Self {
                        -(*self)
                    }
                }

                impl alga::general::TwoSidedInverse<Multiplicative> for [<Decimal$x>] {
                    #[inline]
                    fn two_sided_inverse(&self) -> Self {
                        self.recip()
                    }
                }

                impl alga::linear::NormedSpace for [<Decimal$x>] {
                    type RealField = Self;
                    type ComplexField = Self;

                    #[inline]
                    fn norm_squared(&self) -> Self::RealField {
                        <Self as alga::general::ComplexField>::modulus_squared(*self)
                    }

                    #[inline]
                    fn norm(&self) -> Self::RealField {
                        <Self as alga::general::ComplexField>::modulus(*self)
                    }

                    #[inline]
                    fn normalize(&self) -> Self {
                        *self / self.norm()
                    }

                    #[inline]
                    fn normalize_mut(&mut self) -> Self::RealField {
                        let norm = self.norm();
                        *self /= norm;
                        norm
                    }

                    #[inline]
                    fn try_normalize(&self, eps: Self::RealField) -> Option<Self> {
                        let sq_norm = self.norm_squared();
                        if sq_norm > eps * eps {
                            Some(*self / self.norm())
                        } else {
                            None
                        }
                    }

                    #[inline]
                    fn try_normalize_mut(&mut self, eps: Self::RealField) -> Option<Self::RealField> {
                        let sq_norm = self.norm_squared();
                        if sq_norm > eps * eps {
                            let norm = self.norm();
                            *self /= norm;
                            Some(norm)
                        } else {
                            None
                        }
                    }
                }

                impl alga::linear::VectorSpace for [<Decimal$x>] {
                    type Field = Self;
                }
            };

            #[cfg(feature = "almost")]
            impl almost::AlmostEqual for [<Decimal$x>] {
                type Float = [<Decimal$x>];

                const DEFAULT_TOLERANCE: Self::Float = per_width!($x, d32!(1e-3), d64!(3162277660168379e-23), d128!(3162277660168379331998893544432719e-50));
                const MACHINE_EPSILON: Self::Float = [<Decimal$x>]::EPSILON;

                fn almost_equals_with(self, rhs: Self, tol: Self::Float) -> bool {
                    #[inline]
                    fn eq_with_tol_impl(lhs: [<Decimal$x>], rhs: [<Decimal$x>], tol: [<Decimal$x>]) -> bool {
                        let left_mag = lhs.abs();
                        let right_mag = rhs.abs();
                        if !((left_mag < [<Decimal$x>]::INFINITY) & (right_mag < [<Decimal$x>]::INFINITY)) {
                            false // FIXME handle not finite?
                        } else {
                            let scale = if left_mag > right_mag {
                                left_mag
                            } else {
                                right_mag
                            };
                            // If both left_mag and right_mag are subnormal, rescale to
                            // MIN_POSITIVE instead, which is what they round against anyway.
                            let scale = scale.max([<Decimal$x>]::MIN_POSITIVE);
                            let abs_tol = tol * scale;
                            (lhs - rhs).abs() < abs_tol
                        }
                    }

                    debug_assert!(tol < [<d$x>]!(1.0), "Tolerance should not be greater than 1.0");
                    debug_assert!(tol >= Self::MACHINE_EPSILON, "Tolerance should not be smaller than the machine epsilon");
                    eq_with_tol_impl(self, rhs, tol)
                }

                fn almost_zero_with(self, tol: Self::Float) -> bool {
                    debug_assert!(tol > [<d$x>]!(0.0));
                    self.abs() < tol
                }
            }

            #[cfg(feature = "approx")]
            approx_impl!($x, approx);

            #[cfg(feature = "approx-0_3")]
            approx_impl!($x, approx_0_3);

            #[cfg(feature = "approx-0_4")]
            approx_impl!($x, approx_0_4);

            #[cfg(feature = "arbitrary")]
            const _: () = {
                use arbitrary::{Arbitrary, Result, Unstructured};

                impl<'a> Arbitrary<'a> for [<Decimal$x>] {
                    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                        Ok(Self::from_bits(<[<u$x>] as Arbitrary<'a>>::arbitrary(u)?))
                    }

                    #[inline]
                    fn size_hint(depth: usize) -> (usize, Option<usize>) {
                        <[<u$x>] as Arbitrary<'a>>::size_hint(depth)
                    }
                }
            };

            #[cfg(feature = "bigdecimal")]
            const _: () = {
                use bigdecimal::BigDecimal;

                impl TryFrom<[<Decimal$x>]> for BigDecimal {
                    type Error = bigdecimal::ParseBigDecimalError;

                    #[inline]
                    fn try_from(n: [<Decimal$x>]) -> Result<Self, Self::Error> {
                        BigDecimal::from_str(&n.to_string())
                    }
                }

                impl<'a> Div<[<Decimal$x>]> for &'a BigDecimal {
                    type Output = BigDecimal;

                    #[inline]
                    fn div(self, den: [<Decimal$x>]) -> Self::Output {
                        if den.is_nan() {
                            <BigDecimal as num_traits::Zero>::zero()
                        } else if den == [<d$x>]!(1) {
                            self.clone()
                        } else if den == [<d$x>]!(0.5) {
                            self.double()
                        } else if den == [<d$x>]!(2.0) {
                            self.half()
                        } else if den == [<d$x>]!(-1) {
                            -self
                        } else if den < [<d$x>]!(0) && <BigDecimal as num_traits::Signed>::is_positive(self) {
                            -(self / -den)
                        } else {
                            // Unwrap is safe, because `is_nan` checked above
                            self / BigDecimal::try_from(den).unwrap()
                        }
                    }
                }

                impl<'a> Div<&'a BigDecimal> for [<Decimal$x>] {
                    type Output = BigDecimal;
                    #[inline(always)]
                    fn div(self, den: &'a BigDecimal) -> Self::Output {
                        if self.is_nan() {
                            <BigDecimal as num_traits::Zero>::zero()
                        } else {
                            BigDecimal::try_from(self).unwrap() / den
                        }
                    }
                }

                impl Div<BigDecimal> for [<Decimal$x>] {
                    type Output = BigDecimal;
                    #[inline(always)]
                    fn div(self, den: BigDecimal) -> Self::Output {
                        if self.is_nan() {
                            <BigDecimal as num_traits::Zero>::zero()
                        } else {
                            BigDecimal::try_from(self).unwrap() / den
                        }
                    }
                }
            };

            #[cfg(feature = "borsh")]
            const _: () = {
                use borsh::{de, maybestd::io, ser};

                impl ser::BorshSerialize for [<Decimal$x>] {
                    #[inline]
                    fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
                        writer.write_all(&self.to_bits().to_le_bytes())
                    }
                }

                impl de::BorshDeserialize for [<Decimal$x>] {
                    #[inline]
                    fn deserialize_reader<R: io::Read>(reader: &mut R) -> io::Result<Self> {
                        const SIZE: usize = core::mem::size_of::<[<Decimal$x>]>();
                        let mut buf = [0u8; SIZE];

                        reader.read_exact(&mut buf)?;

                        let res = [<Decimal$x>]::from_bits([<u$x>]::from_le_bytes(
                            buf[..SIZE].try_into().unwrap(),
                        ));

                        Ok(res)
                    }
                }

                // FIXME impl BorshSchema?
            };

            // FIXME impl Contiguous for enums?
            #[cfg(feature = "bytemuck")]
            const _: () = {
                unsafe impl bytemuck::Pod for [<Decimal$x>] {}

                unsafe impl bytemuck::Zeroable for [<Decimal$x>] {}
            };

            #[cfg(feature = "bytecheck")]
            const _: () = {
                impl<C: ?Sized> bytecheck::CheckBytes<C> for [<Decimal$x>] {
                    type Error = Infallible;

                    #[inline]
                    unsafe fn check_bytes<'a>(
                        value: *const Self,
                        _: &mut C,
                    ) -> Result<&'a Self, Self::Error> {
                        Ok(unsafe { &*value })
                    }
                }
            };

            #[cfg(feature = "dec")]
            const _: () = {
                impl From<dec::[<Decimal$x>]> for [<Decimal$x>] {
                    #[inline]
                    fn from(d: dec::[<Decimal$x>]) -> Self {
                        Self::from_ne_bytes_decimal_encoding(d.to_ne_bytes())
                    }
                }

                impl From<[<Decimal$x>]> for dec::[<Decimal$x>] {
                    #[inline]
                    fn from(d: [<Decimal$x>]) -> dec::[<Decimal$x>] {
                        Self::from_ne_bytes(d.to_ne_bytes_decimal_encoding())
                    }
                }
            };

            #[cfg(feature = "decimal")]
            const _: () = {
                only_128!($x,
                    impl From<decimal::d128> for [<Decimal$x>] {
                        #[inline]
                        fn from(d: decimal::d128) -> Self {
                            Self::from_ne_bytes_decimal_encoding(d.to_raw_bytes())
                        }
                    }

                    impl From<[<Decimal$x>]> for decimal::d128 {
                        #[inline]
                        fn from(d: [<Decimal$x>]) -> Self {
                            unsafe { Self::from_raw_bytes(d.to_ne_bytes_decimal_encoding()) }
                        }
                    }
                );
            };

            #[cfg(feature = "decorum")]
            const _: () = {
                impl decorum::Encoding for [<Decimal$x>] {
                    const MIN: Self = [<Decimal$x>]::MIN;
                    const MAX: Self = [<Decimal$x>]::MAX;
                    const MIN_POSITIVE: Self = [<Decimal$x>]::MIN_POSITIVE;
                    const EPSILON: Self = [<Decimal$x>]::EPSILON;
                    trait_forward!($x, classify(self) -> FpCategory);
                    trait_forward!($x, is_normal(self) -> bool);
                    trait_forward!($x, is_sign_positive(self) -> bool);
                    trait_forward!($x, is_sign_negative(self) -> bool);

                    only_32_64!($x,
                        /// Returns the significand, base 10 exponent, and sign as integers, respectively.
                        /// The original number can be recovered by sign * significand * 10 ^ exponent.
                        #[inline]
                        fn integer_decode(self) -> (u64, i16, i8) {
                            let (significand, exponent, signed) = [<Decimal$x>]::integer_decode(self);
                            (significand as u64, exponent, if signed { -1 } else { 1 })
                        }
                    );

                    // FIXME a better way?
                    only_128!($x,
                        /// **Unimplemented**
                        /// This method can't be implemented because a `u64` isn't big enough to fit the significand.
                        ///
                        /// # Panics
                        /// Always panics.
                        fn integer_decode(self) -> (u64, i16, i8) {
                            unimplemented!("`integer_decode` is not implemented for `Decimal128`")
                        }
                    );
                }

                impl decorum::Infinite for [<Decimal$x>] {
                    const INFINITY: Self = [<Decimal$x>]::INFINITY;
                    const NEG_INFINITY: Self = [<Decimal$x>]::NEG_INFINITY;
                    trait_forward!($x, is_infinite(self) -> bool);
                    trait_forward!($x, is_finite(self) -> bool);
                }

                impl decorum::Nan for [<Decimal$x>] {
                    const NAN: Self = [<Decimal$x>]::NAN;
                    trait_forward!($x, is_nan(self) -> bool);
                }

                only_32_64!($x,
                    impl decorum::ToCanonicalBits for [<Decimal$x>] {
                        fn to_canonical_bits(self) -> u64 {
                            let result = self.convert_into::<Decimal64>();
                            (if result.is_nan() {
                                Decimal64::NAN
                            } else if result == d64!(0) {
                                d64!(0)
                            } else {
                                result
                            }).to_bits()
                        }
                    }
                );

                impl decorum::cmp::FloatEq for [<Decimal$x>] {
                    fn float_eq(&self, other: &Self) -> bool {
                        <[<Decimal$x>] as decorum::cmp::FloatOrd>::float_cmp(self, other) == Ordering::Equal
                    }
                }

                impl decorum::cmp::FloatOrd for [<Decimal$x>] {
                    fn float_cmp(&self, other: &Self) -> Ordering {
                        match self.partial_cmp(&other) {
                            Some(ordering) => ordering,
                            None => {
                                if self.is_nan() {
                                    if other.is_nan() {
                                        Ordering::Equal
                                    }
                                    else {
                                        Ordering::Greater
                                    }
                                }
                                else {
                                    Ordering::Less
                                }
                            }
                        }
                    }
                }

                impl decorum::cmp::IntrinsicOrd for [<Decimal$x>] {
                    fn is_undefined(&self) -> bool {
                        self.is_nan()
                    }

                    fn min_max_or_undefined(&self, other: &Self) -> (Self, Self) {
                        match self.partial_cmp(other) {
                            Some(ordering) => match ordering {
                                Ordering::Less | Ordering::Equal => (*self, *other),
                                _ => (*other, *self),
                            },
                            _ => ([<Decimal$x>]::NAN, [<Decimal$x>]::NAN),
                        }
                    }
                }

                impl decorum::hash::FloatHash for [<Decimal$x>] {
                    fn hash<H>(&self, state: &mut H)
                    where
                        H: core::hash::Hasher,
                    {
                        let result = self.convert_into::<[<Decimal$x>]>();
                        let bits = (if result.is_nan() {
                            [<Decimal$x>]::NAN
                        } else if result == [<d$x>]!(0) {
                            [<d$x>]!(0)
                        } else {
                            result
                        }).to_bits();
                        <[<u$x>] as core::hash::Hash>::hash(&bits, state);
                    }
                }
            };

            #[cfg(feature = "euclid")]
            const _: () = {
                impl euclid::approxeq::ApproxEq<Self> for [<Decimal$x>] {
                    #[inline]
                    fn approx_epsilon() -> Self {
                        [<Decimal$x>]::EPSILON
                    }

                    #[inline]
                    fn approx_eq_eps(&self, other: &Self, approx_epsilon: &Self) -> bool {
                        (*self - *other).abs() < *approx_epsilon
                    }
                }

                impl euclid::num::Ceil for [<Decimal$x>] {
                    trait_forward!($x, ceil(self) -> Self);
                }

                impl euclid::num::Floor for [<Decimal$x>] {
                    trait_forward!($x, floor(self) -> Self);
                }

                impl euclid::num::Round for [<Decimal$x>] {
                    trait_forward!($x, round(self) -> Self);
                }

                impl euclid::Trig for [<Decimal$x>] {
                    trait_forward!($x, sin(self) -> Self);
                    trait_forward!($x, cos(self) -> Self);
                    trait_forward!($x, tan(self) -> Self);

                    #[inline]
                    fn fast_atan2(y: Self, x: Self) -> Self {
                        y.atan2(x)
                    }

                    #[inline]
                    fn degrees_to_radians(deg: Self) -> Self {
                        deg.to_radians()
                    }

                    #[inline]
                    fn radians_to_degrees(rad: Self) -> Self {
                        rad.to_degrees()
                    }
                }
            };

            #[cfg(feature = "fake")]
            const _: () = {
                use fake::{Faker, Dummy};
                use rand::Rng;

                impl Dummy<Self> for [<Decimal$x>] {
                    fn dummy(t: &Self) -> Self {
                        t.clone()
                    }

                    fn dummy_with_rng<R: Rng + ?Sized>(t: &Self, _rng: &mut R) -> Self {
                        t.clone()
                    }
                }

                impl fake::Dummy<Faker> for [<Decimal$x>] {
                    fn dummy_with_rng<R: Rng + ?Sized>(_: &Faker, rng: &mut R) -> Self {
                        rng.gen()
                    }
                }

                // FIXME uniform, range
            };

            #[cfg(feature = "float_eq")]
            const _: () = {
                use float_eq::{AssertFloatEq, AssertFloatEqAll, DebugUlpsDiff, FloatEq, FloatEqAll, FloatEqDebugUlpsDiff, FloatEqUlpsTol, UlpsTol};

                impl FloatEqUlpsTol for [<Decimal$x>] {
                    type UlpsTol = [<u$x>];
                }

                impl FloatEqDebugUlpsDiff for [<Decimal$x>] {
                    type DebugUlpsDiff = Option<[<u$x>]>;
                }

                impl FloatEq for [<Decimal$x>] {
                    type Tol = Self;

                    #[inline]
                    fn eq_abs(&self, other: &Self, tol: &Self::Tol) -> bool {
                        // the PartialEq check covers equality of infinities
                        self == other || (self - other).abs() <= *tol
                    }

                    #[inline]
                    fn eq_rmax(&self, other: &Self, tol: &Self::Tol) -> bool {
                        // the PartialEq check covers equality of infinities
                        self == other || {
                            let largest = self.abs().max(other.abs());
                            let tol = largest * tol;
                            (self - other).abs() <= tol
                        }
                    }

                    #[inline]
                    fn eq_rmin(&self, other: &Self, tol: &Self::Tol) -> bool {
                        // the PartialEq check covers equality of infinities
                        self == other || {
                            let largest = self.abs().min(other.abs());
                            let tol = largest * tol;
                            (self - other).abs() <= tol
                        }
                    }

                    #[inline]
                    fn eq_r1st(&self, other: &Self, tol: &Self::Tol) -> bool {
                        // the PartialEq check covers equality of infinities
                        self == other || {
                            let tol = self.abs() * tol;
                            (self - other).abs() <= tol
                        }
                    }

                    #[inline]
                    fn eq_r2nd(&self, other: &Self, tol: &Self::Tol) -> bool {
                        // the PartialEq check covers equality of infinities
                        self == other || {
                            let tol = other.abs() * tol;
                            (self - other).abs() <= tol
                        }
                    }

                    #[inline]
                    fn eq_ulps(&self, other: &Self, tol: &UlpsTol<Self::Tol>) -> bool {
                        if self.is_nan() || other.is_nan() {
                            false // NaNs are never equal
                        } else {
                            let (l, r) = (*self, *other);

                            // Trivial negative sign check
                            let (self_abs, other_abs) = match (l.is_sign_positive(), r.is_sign_positive()) {
                                (true, true) => (l, r),
                                (false, false) => (-l, -r),
                                _ => return false,
                            };

                            // ULPS difference comparison
                            let diff = self_abs - other_abs;
                            let (abs_diff, max);
                            if diff.is_sign_positive() {
                                (abs_diff, max) = (diff, self_abs);
                            } else {
                                (abs_diff, max) = (-diff, other_abs);
                            }

                            let one_ulp = max - Context::new().next_down(max);

                            let max_ulps: Self = [<Decimal$x>]::from_int(*tol);

                            abs_diff <= (max_ulps * one_ulp)
                        }
                    }
                }

                impl FloatEqAll for [<Decimal$x>] {
                    type AllTol = Self;

                    #[inline]
                    fn eq_abs_all(&self, other: &Self, tol: &Self::AllTol) -> bool {
                        self.eq_abs(other, tol)
                    }

                    #[inline]
                    fn eq_rmax_all(&self, other: &Self, tol: &Self::AllTol) -> bool {
                        self.eq_rmax(other, tol)
                    }

                    #[inline]
                    fn eq_rmin_all(&self, other: &Self, tol: &Self::AllTol) -> bool {
                        self.eq_rmin(other, tol)
                    }

                    #[inline]
                    fn eq_r1st_all(&self, other: &Self, tol: &Self::AllTol) -> bool {
                        self.eq_r1st(other, tol)
                    }

                    #[inline]
                    fn eq_r2nd_all(&self, other: &Self, tol: &Self::AllTol) -> bool {
                        self.eq_r2nd(other, tol)
                    }

                    #[inline]
                    fn eq_ulps_all(&self, other: &Self, tol: &UlpsTol<Self::AllTol>) -> bool {
                        self.eq_ulps(other, tol)
                    }
                }

                impl AssertFloatEq for [<Decimal$x>] {
                    type DebugAbsDiff = Self;
                    type DebugTol = Self::Tol;

                    #[inline]
                    fn debug_abs_diff(&self, other: &Self) -> Self::DebugAbsDiff {
                        (self - other).abs()
                    }

                    #[inline]
                    fn debug_ulps_diff(&self, other: &Self) -> DebugUlpsDiff<Self::DebugAbsDiff> {
                        if self == other {
                            Some(0)
                        } else if self.is_nan() || other.is_nan() {
                            None
                        } else {
                            let (l, r) = (*self, *other);

                            // Trivial negative sign check
                            let (self_abs, other_abs) = match (l.is_sign_positive(), r.is_sign_positive()) {
                                (true, true) => (l, r),
                                (false, false) => (-l, -r),
                                _ => return None,
                            };

                            // ULPS difference comparison
                            let diff = self_abs - other_abs;
                            let (abs_diff, max);
                            if diff.is_sign_positive() {
                                (abs_diff, max) = (diff, self_abs);
                            } else {
                                (abs_diff, max) = (-diff, other_abs);
                            }

                            let one_ulp = max - Context::new().next_down(max);

                            Some((abs_diff / one_ulp).to_int())
                        }
                    }

                    #[inline]
                    fn debug_abs_tol(&self, _other: &Self, tol: &Self::Tol) -> Self::DebugTol {
                        *tol
                    }

                    #[inline]
                    fn debug_rmax_tol(&self, other: &Self, tol: &Self::Tol) -> Self::DebugTol {
                        self.abs().max(other.abs()) * tol
                    }

                    #[inline]
                    fn debug_rmin_tol(&self, other: &Self, tol: &Self::Tol) -> Self::DebugTol {
                        self.abs().min(other.abs()) * tol
                    }

                    #[inline]
                    fn debug_r1st_tol(&self, _other: &Self, tol: &Self::Tol) -> Self::DebugTol {
                        self.abs() * tol
                    }

                    #[inline]
                    fn debug_r2nd_tol(&self, other: &Self, tol: &Self::Tol) -> Self::DebugTol {
                        other.abs() * tol
                    }

                    #[inline]
                    fn debug_ulps_tol(
                        &self,
                        _other: &Self,
                        tol: &UlpsTol<Self::Tol>,
                    ) -> UlpsTol<Self::DebugTol> {
                        *tol
                    }
                }

                impl AssertFloatEqAll for [<Decimal$x>] {
                    type AllDebugTol = Self::AllTol;

                    #[inline]
                    fn debug_abs_all_tol(&self, other: &Self, tol: &Self::AllTol) -> Self::AllDebugTol {
                        self.debug_abs_tol(other, tol)
                    }

                    #[inline]
                    fn debug_rmax_all_tol(&self, other: &Self, tol: &Self::AllTol) -> Self::AllDebugTol {
                        self.debug_rmax_tol(other, tol)
                    }

                    #[inline]
                    fn debug_rmin_all_tol(&self, other: &Self, tol: &Self::AllTol) -> Self::AllDebugTol {
                        self.debug_rmin_tol(other, tol)
                    }

                    #[inline]
                    fn debug_r1st_all_tol(&self, other: &Self, tol: &Self::AllTol) -> Self::AllDebugTol {
                        self.debug_r1st_tol(other, tol)
                    }

                    #[inline]
                    fn debug_r2nd_all_tol(&self, other: &Self, tol: &Self::AllTol) -> Self::AllDebugTol {
                        self.debug_r2nd_tol(other, tol)
                    }

                    #[inline]
                    fn debug_ulps_all_tol(
                        &self,
                        other: &Self,
                        tol: &UlpsTol<Self::AllTol>,
                    ) -> UlpsTol<Self::AllDebugTol> {
                        self.debug_ulps_tol(other, tol)
                    }
                }
            };

            #[cfg(feature = "float_next_after")]
            impl float_next_after::NextAfter for [<Decimal$x>] {
                fn next_after(self, y: [<Decimal$x>]) -> [<Decimal$x>] {
                    Context::new().next_after(self, y)
                }
            }


            #[cfg(feature = "funty")]
            const _: () = {
                impl funty::AtLeast8 for [<Decimal$x>] {}
                impl funty::AtLeast16 for [<Decimal$x>] {}
                impl funty::AtLeast32 for [<Decimal$x>] {}

                only_32!($x,
                    only_32!($x,
                        impl funty::AtMost32 for [<Decimal$x>] {}
                        impl funty::Is32 for [<Decimal$x>] {}
                    );
                );

                only_32_64!($x,
                    impl funty::AtMost64 for [<Decimal$x>] {}
                );

                only_64!($x,
                    impl funty::Is64 for [<Decimal$x>] {}
                );

                only_64_128!($x,
                    impl funty::AtLeast64 for [<Decimal$x>] {}
                );

                only_128!($x,
                    impl funty::AtLeast128 for [<Decimal$x>] {}
                    impl funty::Is128 for [<Decimal$x>] {}
                );

                impl funty::AtMost128 for [<Decimal$x>] {}

                // FIXME funty::Floating? (need From<f32>)

                impl funty::Fundamental for [<Decimal$x>] {
                    #[inline]
                    fn as_bool(self) -> bool {
                        self.is_zero()
                    }

                    #[inline]
                    fn as_char(self) -> Option<char> {
                        char::from_u32(self.as_u32())
                    }

                    as_to_int_fn!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize);
                    fn as_f32(self) -> f32 { Context::new().convert_format(self) }
                    fn as_f64(self) -> f64 { Context::new().convert_format(self) }
                }

                impl funty::Numeric for [<Decimal$x>] {
                    type Bytes = [u8; $x / 8];

                    trait_forward!($x, to_be_bytes(self) -> Self::Bytes);
                    trait_forward!($x, to_le_bytes(self) -> Self::Bytes);
                    trait_forward!($x, to_ne_bytes(self) -> Self::Bytes);
                    trait_forward!($x, from_be_bytes(bytes: Self::Bytes) -> Self);
                    trait_forward!($x, from_le_bytes(bytes: Self::Bytes) -> Self);
                    trait_forward!($x, from_ne_bytes(bytes: Self::Bytes) -> Self);
                }
            };

            #[cfg(feature = "gc")]
            const _: () = {
                impl gc::Finalize for [<Decimal$x>] {}

                // Safety: `[<Decimal$x>]` is `Copy` and has nothing to drop
                unsafe impl gc::Trace for [<Decimal$x>] {
                    #[inline]
                    unsafe fn trace(&self) {}
                    #[inline]
                    unsafe fn root(&self) {}
                    #[inline]
                    unsafe fn unroot(&self) {}
                    #[inline]
                    fn finalize_glue(&self) {
                        gc::Finalize::finalize(self)
                    }
                }
            };

            #[cfg(feature = "lyon_geom")]
            const _: () = {
                impl lyon_geom::Scalar for [<Decimal$x>] {
                    const HALF: Self = [<d$x>]!(0.5);
                    const ZERO: Self = [<d$x>]!(0);
                    const ONE: Self = [<d$x>]!(1);
                    const TWO: Self = [<d$x>]!(2);
                    const THREE: Self = [<d$x>]!(3);
                    const FOUR: Self = [<d$x>]!(4);
                    const FIVE: Self = [<d$x>]!(5);
                    const SIX: Self = [<d$x>]!(6);
                    const SEVEN: Self = [<d$x>]!(7);
                    const EIGHT: Self = [<d$x>]!(8);
                    const NINE: Self = [<d$x>]!(9);
                    const TEN: Self = [<d$x>]!(10);
                    const EPSILON: Self = [<Decimal$x>]::EPSILON;
                    const MIN: Self = [<Decimal$x>]::MIN;
                    const MAX: Self = [<Decimal$x>]::MAX;

                    fn value(v: f32) -> Self {
                        [<Decimal$x>]::convert_from(v)
                    }

                    // FIXME are these too small? or is the constant? maybe a bigger number when near zero?
                    fn epsilon_for(reference: Self) -> Self {
                        let relative_ulp = if reference.is_sign_positive() {
                            Context::new().next_up(reference) - reference
                        } else {
                            reference - Context::new().next_down(reference)
                        };

                        relative_ulp.max(Self::EPSILON)
                    }
                }
            };

            #[cfg(feature = "ndarray")]
            const _: () = {
                impl ndarray::NdFloat for [<Decimal$x>] {}
                impl ndarray::ScalarOperand for [<Decimal$x>] {}
            };

            #[cfg(feature = "ndarray-stats")]
            const _: () = {
                use ndarray::{s, ArrayViewMut1};
                use ndarray_stats::MaybeNan;
                use noisy_float::{checkers::NumChecker, NoisyFloat};

                impl MaybeNan for [<Decimal$x>] {
                    type NotNan = NoisyFloat<[<Decimal$x>], NumChecker>;

                    fn is_nan(&self) -> bool {
                        [<Decimal$x>]::is_nan(*self)
                    }

                    fn try_as_not_nan(&self) -> Option<&Self::NotNan> {
                        Self::NotNan::try_borrowed(self)
                    }

                    fn from_not_nan(value: Self::NotNan) -> Self {
                        value.raw()
                    }

                    fn from_not_nan_opt(value: Option<Self::NotNan>) -> Self {
                        match value {
                            None => [<Decimal$x>]::NAN,
                            Some(num) => num.raw(),
                        }
                    }

                    fn from_not_nan_ref_opt(value: Option<&Self::NotNan>) -> &Self {
                        match value {
                            None => &[<Decimal$x>]::NAN,
                            Some(num) => num.as_ref(),
                        }
                    }

                    fn remove_nan_mut(view: ArrayViewMut1<'_, Self>) -> ArrayViewMut1<'_, Self::NotNan> {
                        /// Returns a view with the NaN values removed.
                        ///
                        /// This modifies the input view by moving elements as necessary.
                        fn remove_nan_mut<A: MaybeNan>(mut view: ArrayViewMut1<'_, A>) -> ArrayViewMut1<'_, A> {
                            if view.is_empty() {
                                return view.slice_move(s![..0]);
                            }
                            let mut i = 0;
                            let mut j = view.len() - 1;
                            loop {
                                // At this point, `i == 0 || !view[i-1].is_nan()`
                                // and `j == view.len() - 1 || view[j+1].is_nan()`.
                                while i <= j && !view[i].is_nan() {
                                    i += 1;
                                }
                                // At this point, `view[i].is_nan() || i == j + 1`.
                                while j > i && view[j].is_nan() {
                                    j -= 1;
                                }
                                // At this point, `!view[j].is_nan() || j == i`.
                                if i >= j {
                                    return view.slice_move(s![..i]);
                                }

                                view.swap(i, j);
                                i += 1;
                                j -= 1;
                            }
                        }

                        let not_nan = remove_nan_mut(view);
                        // This is safe because `remove_nan_mut` has removed the NaN
                        // values, and `Self::NotNan` is a thin wrapper around `Self`.
                        unsafe {
                            ArrayViewMut1::from_shape_ptr(not_nan.dim(), not_nan.as_ptr() as *mut Self::NotNan)
                        }
                    }
                }
            };

            #[cfg(feature = "num-bigint")]
            const _: () = {
                impl num_bigint::ToBigUint for [<Decimal$x>] {
                    #[inline]
                    fn to_biguint(&self) -> Option<num_bigint::BigUint> {
                        let mut n = *self;
                        if !n.is_finite() {
                            return None;
                        }

                        // match the rounding of casting from float to int
                        n = n.trunc();

                        // handle 0.x, -0.x
                        if n.is_zero() {
                            return Some(<num_bigint::BigUint as num_traits::Zero>::zero());
                        }

                        let (significand, exponent, signed) = [<Decimal$x>]::integer_decode(n);

                        if signed {
                            return None;
                        }

                        let mut ret = num_bigint::BigUint::from(significand);
                        match exponent.cmp(&0) {
                            Ordering::Greater => ret *= num_bigint::BigUint::from(10_u16).pow(exponent as u32),
                            Ordering::Equal => {}
                            Ordering::Less => ret /= num_bigint::BigUint::from(10_u16).pow(-exponent as u32),
                        }
                        Some(ret)
                    }
                }

                impl num_bigint::ToBigInt for [<Decimal$x>] {
                    #[inline]
                    fn to_bigint(&self) -> Option<num_bigint::BigInt> {
                        let n = *self;
                        if n.is_sign_positive() {
                            <[<Decimal$x>] as num_bigint::ToBigUint>::to_biguint(&n)
                                .map(num_bigint::BigInt::from)
                        } else {
                            let x = <[<Decimal$x>] as num_bigint::ToBigUint>::to_biguint(&(-n))?;
                            Some(-num_bigint::BigInt::from(x))
                        }
                    }
                }
            };

            #[cfg(feature = "num-complex")]
            const _: () = {
                use num_complex::Complex;
                use num_traits::*;

                impl<'a, T: Float> Pow<[<Decimal$x>]> for &'a Complex<T>
                where
                    [<Decimal$x>]: Into<T>,
                {
                    type Output = Complex<T>;

                    #[inline]
                    fn pow(self, exp: [<Decimal$x>]) -> Self::Output {
                        self.powf(exp.into())
                    }
                }

                impl<'a, 'b, T: Float> Pow<&'b [<Decimal$x>]> for &'a Complex<T>
                where
                    [<Decimal$x>]: Into<T>,
                {
                    type Output = Complex<T>;

                    #[inline]
                    fn pow(self, &exp: &[<Decimal$x>]) -> Self::Output {
                        self.powf(exp.into())
                    }
                }

                impl<T: Float> Pow<[<Decimal$x>]> for Complex<T>
                where
                    [<Decimal$x>]: Into<T>,
                {
                    type Output = Complex<T>;

                    #[inline]
                    fn pow(self, exp: [<Decimal$x>]) -> Self::Output {
                        self.powf(exp.into())
                    }
                }

                impl<'b, T: Float> Pow<&'b [<Decimal$x>]> for Complex<T>
                where
                    [<Decimal$x>]: Into<T>,
                {
                    type Output = Complex<T>;

                    #[inline]
                    fn pow(self, &exp: &[<Decimal$x>]) -> Self::Output {
                        self.powf(exp.into())
                    }
                }

                #[cfg(feature = "alga")]
                const _: () = {
                    impl<N2: Zero + alga::general::SupersetOf<[<Decimal$x>]>> alga::general::SubsetOf<Complex<N2>> for [<Decimal$x>] {
                        #[inline]
                        fn to_superset(&self) -> Complex<N2> {
                            Complex {
                                re: N2::from_subset(self),
                                im: N2::zero()
                            }
                        }

                        #[inline]
                        unsafe fn from_superset_unchecked(element: &Complex<N2>) -> Self {
                            unsafe {
                                element.re.to_subset_unchecked()
                            }
                        }

                        #[inline]
                        fn is_in_subset(c: &Complex<N2>) -> bool {
                            c.re.is_in_subset() && c.im.is_zero()
                        }
                    }
                };

                #[cfg(feature = "simba")]
                const _: () = {
                    impl<N2: Zero + simba::scalar::SupersetOf<[<Decimal$x>]>> simba::scalar::SubsetOf<Complex<N2>> for [<Decimal$x>] {
                        #[inline]
                        fn to_superset(&self) -> Complex<N2> {
                            Complex {
                                re: N2::from_subset(self),
                                im: N2::zero()
                            }
                        }

                        #[inline]
                        fn from_superset_unchecked(element: &Complex<N2>) -> Self {
                            element.re.to_subset_unchecked()
                        }

                        #[inline]
                        fn is_in_subset(c: &Complex<N2>) -> bool {
                            c.re.is_in_subset() && c.im.is_zero()
                        }
                    }
                };
            };

            #[cfg(feature = "num-dual")]
            impl num_dual::DualNum<Self> for [<Decimal$x>] {
                const NDERIV: usize = 0;

                fn re(&self) -> [<Decimal$x>] {
                    *self
                }

                fn scale(&mut self, f: [<Decimal$x>]) {
                    *self *= f;
                }

                fn mul_add(&self, a: Self, b: Self) -> Self {
                    [<Decimal$x>]::mul_add(*self, a, b)
                }
                fn recip(&self) -> Self {
                    [<Decimal$x>]::recip(*self)
                }
                fn powi(&self, n: i32) -> Self {
                    [<Decimal$x>]::powi(*self, n)
                }
                fn powf(&self, n: Self) -> Self {
                    [<Decimal$x>]::powf(*self, n)
                }
                fn powd(&self, n: Self) -> Self {
                    [<Decimal$x>]::powf(*self, n)
                }
                fn sqrt(&self) -> Self {
                    [<Decimal$x>]::sqrt(*self)
                }
                fn exp(&self) -> Self {
                    [<Decimal$x>]::exp(*self)
                }
                fn exp2(&self) -> Self {
                    [<Decimal$x>]::exp2(*self)
                }
                fn ln(&self) -> Self {
                    [<Decimal$x>]::ln(*self)
                }
                fn log(&self, base: Self) -> Self {
                    [<Decimal$x>]::log(*self, base)
                }
                fn log2(&self) -> Self {
                    [<Decimal$x>]::log2(*self)
                }
                fn log10(&self) -> Self {
                    [<Decimal$x>]::log10(*self)
                }
                fn cbrt(&self) -> Self {
                    [<Decimal$x>]::cbrt(*self)
                }
                fn sin(&self) -> Self {
                    [<Decimal$x>]::sin(*self)
                }
                fn cos(&self) -> Self {
                    [<Decimal$x>]::cos(*self)
                }
                fn tan(&self) -> Self {
                    [<Decimal$x>]::tan(*self)
                }
                fn asin(&self) -> Self {
                    [<Decimal$x>]::asin(*self)
                }
                fn acos(&self) -> Self {
                    [<Decimal$x>]::acos(*self)
                }
                fn atan(&self) -> Self {
                    [<Decimal$x>]::atan(*self)
                }
                fn sin_cos(&self) -> (Self, Self) {
                    [<Decimal$x>]::sin_cos(*self)
                }
                fn exp_m1(&self) -> Self {
                    [<Decimal$x>]::exp_m1(*self)
                }
                fn ln_1p(&self) -> Self {
                    [<Decimal$x>]::ln_1p(*self)
                }
                fn sinh(&self) -> Self {
                    [<Decimal$x>]::sinh(*self)
                }
                fn cosh(&self) -> Self {
                    [<Decimal$x>]::cosh(*self)
                }
                fn tanh(&self) -> Self {
                    [<Decimal$x>]::tanh(*self)
                }
                fn asinh(&self) -> Self {
                    [<Decimal$x>]::asinh(*self)
                }
                fn acosh(&self) -> Self {
                    [<Decimal$x>]::acosh(*self)
                }
                fn atanh(&self) -> Self {
                    [<Decimal$x>]::atanh(*self)
                }
                fn sph_j0(&self) -> Self {
                    if self.abs() < [<Decimal$x>]::EPSILON {
                        [<d$x>]!(1.0) - self * self / [<d$x>]!(6.0)
                    } else {
                        self.sin() / self
                    }
                }
                fn sph_j1(&self) -> Self {
                    if self.abs() < [<Decimal$x>]::EPSILON {
                        self / [<d$x>]!(3.0)
                    } else {
                        let sc = self.sin_cos();
                        let rec = self.recip();
                        (sc.0 * rec - sc.1) * rec
                    }
                }
                fn sph_j2(&self) -> Self {
                    if self.abs() < [<Decimal$x>]::EPSILON {
                        self * self / [<d$x>]!(15.0)
                    } else {
                        let sc = self.sin_cos();
                        let s2 = self * self;
                        (([<d$x>]!(3.0) - s2) * sc.0 - [<d$x>]!(3.0) * self * sc.1) / (self * s2)
                    }
                }
            }

            #[cfg(feature = "num-traits")]
            const _: () = {
                use num_traits::*;
                use forward_ref::forward_ref_unop;

                impl Bounded for [<Decimal$x>] {
                    trait_forward_const!($x, min_value() -> Self { MIN });
                    trait_forward_const!($x, max_value() -> Self { MAX });
                }

                // https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast

                impl FromPrimitive for [<Decimal$x>] {
                    from_primitive_int!($x, [u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize]);
                    from_primitive_float!($x, [f32, f64]);
                }

                impl ToPrimitive for [<Decimal$x>] {
                    to_primitive_to_int_fn!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128);

                    #[inline]
                    fn to_f32(&self) -> Option<f32> {
                        Some(Context::new().convert_format(*self))
                    }

                    #[inline]
                    fn to_f64(&self) -> Option<f64> {
                        Some(Context::new().convert_format(*self))
                    }
                }

                impl NumCast for [<Decimal$x>] {
                    /// Convert the operand to `f64`, and then convert that to
                    #[doc = "`Decimal" $x "`."]
                    #[inline]
                    fn from<T: ToPrimitive>(n: T) -> Option<Self> {
                        Self::from_f64(n.to_f64()?)
                    }
                }

                impl float::FloatCore for [<Decimal$x>] {
                    trait_forward_const!($x, infinity() -> Self { INFINITY });
                    trait_forward_const!($x, neg_infinity() -> Self { NEG_INFINITY });
                    trait_forward_const!($x, nan() -> Self { NAN });
                    #[inline]
                    fn neg_zero() -> Self {
                        [<d$x>]!(-0)
                    }
                    trait_forward_const!($x, min_value() -> Self { MIN });
                    trait_forward_const!($x, min_positive_value() -> Self { MIN_POSITIVE });
                    trait_forward_const!($x, epsilon() -> Self { EPSILON });
                    trait_forward_const!($x, max_value() -> Self { MAX });
                    trait_forward!($x, classify(self) -> FpCategory);
                    trait_forward!($x, to_degrees(self) -> Self);
                    trait_forward!($x, to_radians(self) -> Self);

                    only_32_64!($x,
                        /// Returns the significand, base 10 exponent, and sign as integers, respectively.
                        /// The original number can be recovered by sign * significand * 10 ^ exponent.
                        #[inline]
                        fn integer_decode(self) -> (u64, i16, i8) {
                            let (significand, exponent, signed) = [<Decimal$x>]::integer_decode(self);
                            (significand as u64, exponent, if signed { -1 } else { 1 })
                        }
                    );

                    // FIXME a better way?
                    only_128!($x,
                        /// **Unimplemented**
                        /// This method can't be implemented because a `u64` isn't big enough to fit the significand.
                        ///
                        /// # Panics
                        /// Always panics.
                        fn integer_decode(self) -> (u64, i16, i8) {
                            unimplemented!("`integer_decode` is not implemented for `Decimal128`")
                        }
                    );

                    trait_forward!($x, is_nan(self) -> bool);
                    trait_forward!($x, is_infinite(self) -> bool);
                    trait_forward!($x, is_finite(self) -> bool);
                    trait_forward!($x, is_normal(self) -> bool);
                    trait_forward!($x, floor(self) -> Self);
                    trait_forward!($x, ceil(self) -> Self);
                    trait_forward!($x, round(self) -> Self);
                    trait_forward!($x, trunc(self) -> Self);
                    trait_forward!($x, fract(self) -> Self);
                    trait_forward!($x, abs(self) -> Self);
                    trait_forward!($x, signum(self) -> Self);
                    trait_forward!($x, is_sign_positive(self) -> bool);
                    trait_forward!($x, is_sign_negative(self) -> bool);
                    trait_forward!($x, min(self, other: Self) -> Self);
                    trait_forward!($x, max(self, other: Self) -> Self);
                    trait_forward!($x, recip(self) -> Self);
                    trait_forward!($x, powi(self, n: i32) -> Self);
                }

                impl Float for [<Decimal$x>] {
                    trait_forward_const!($x, nan() -> Self { NAN });
                    trait_forward_const!($x, infinity() -> Self { INFINITY });
                    trait_forward_const!($x, neg_infinity() -> Self { NEG_INFINITY });
                    #[inline]
                    fn neg_zero() -> Self {
                        [<d$x>]!(-0)
                    }
                    trait_forward_const!($x, min_value() -> Self { MIN });
                    trait_forward_const!($x, min_positive_value() -> Self { MIN_POSITIVE });
                    trait_forward_const!($x, max_value() -> Self { MAX });
                    trait_forward!($x, is_nan(self) -> bool);
                    trait_forward!($x, is_infinite(self) -> bool);
                    trait_forward!($x, is_finite(self) -> bool);
                    trait_forward!($x, is_normal(self) -> bool);
                    trait_forward!($x, classify(self) -> FpCategory);
                    trait_forward!($x, floor(self) -> Self);
                    trait_forward!($x, ceil(self) -> Self);
                    trait_forward!($x, round(self) -> Self);
                    trait_forward!($x, trunc(self) -> Self);
                    trait_forward!($x, fract(self) -> Self);
                    trait_forward!($x, abs(self) -> Self);
                    trait_forward!($x, signum(self) -> Self);
                    trait_forward!($x, is_sign_positive(self) -> bool);
                    trait_forward!($x, is_sign_negative(self) -> bool);
                    trait_forward!($x, mul_add(self, a: Self, b: Self) -> Self);
                    trait_forward!($x, recip(self) -> Self);
                    trait_forward!($x, powi(self, n: i32) -> Self);
                    trait_forward!($x, powf(self, n: Self) -> Self);
                    trait_forward!($x, sqrt(self) -> Self);
                    trait_forward!($x, exp(self) -> Self);
                    trait_forward!($x, exp2(self) -> Self);
                    trait_forward!($x, ln(self) -> Self);
                    trait_forward!($x, log(self, base: Self) -> Self);
                    trait_forward!($x, log2(self) -> Self);
                    trait_forward!($x, log10(self) -> Self);
                    trait_forward!($x, max(self, other: Self) -> Self);
                    trait_forward!($x, min(self, other: Self) -> Self);
                    trait_forward!($x, #[allow(deprecated)] abs_sub(self, other: Self) -> Self);
                    trait_forward!($x, cbrt(self) -> Self);
                    trait_forward!($x, hypot(self, other: Self) -> Self);
                    trait_forward!($x, sin(self) -> Self);
                    trait_forward!($x, cos(self) -> Self);
                    trait_forward!($x, tan(self) -> Self);
                    trait_forward!($x, asin(self) -> Self);
                    trait_forward!($x, acos(self) -> Self);
                    trait_forward!($x, atan(self) -> Self);
                    trait_forward!($x, atan2(self, other: Self) -> Self);
                    trait_forward!($x, sin_cos(self) -> (Self, Self));
                    trait_forward!($x, exp_m1(self) -> Self);
                    trait_forward!($x, ln_1p(self) -> Self);
                    trait_forward!($x, sinh(self) -> Self);
                    trait_forward!($x, cosh(self) -> Self);
                    trait_forward!($x, tanh(self) -> Self);
                    trait_forward!($x, asinh(self) -> Self);
                    trait_forward!($x, acosh(self) -> Self);
                    trait_forward!($x, atanh(self) -> Self);

                    #[inline]
                    fn integer_decode(self) -> (u64, i16, i8) {
                        <Self as float::FloatCore>::integer_decode(self)
                    }

                    trait_forward_const!($x, epsilon() -> Self { EPSILON });
                    trait_forward!($x, to_degrees(self) -> Self);
                    trait_forward!($x, to_radians(self) -> Self);
                }

                impl FloatConst for [<Decimal$x>] {
                    trait_forward_const_math!($x, E);
                    trait_forward_const_math!($x, FRAC_1_PI);
                    trait_forward_const_math!($x, FRAC_1_SQRT_2);
                    trait_forward_const_math!($x, FRAC_2_PI);
                    trait_forward_const_math!($x, FRAC_2_SQRT_PI);
                    trait_forward_const_math!($x, FRAC_PI_2);
                    trait_forward_const_math!($x, FRAC_PI_3);
                    trait_forward_const_math!($x, FRAC_PI_4);
                    trait_forward_const_math!($x, FRAC_PI_6);
                    trait_forward_const_math!($x, FRAC_PI_8);
                    trait_forward_const_math!($x, LN_10);
                    trait_forward_const_math!($x, LN_2);
                    trait_forward_const_math!($x, LOG10_E);
                    trait_forward_const_math!($x, LOG2_E);
                    trait_forward_const_math!($x, PI);
                    trait_forward_const_math!($x, SQRT_2);
                    trait_forward_const_math!($x, TAU);
                    trait_forward_const_math!($x, LOG10_2);
                    trait_forward_const_math!($x, LOG2_10);
                }

                impl One for [<Decimal$x>] {
                    #[inline]
                    fn one() -> Self {
                        [<d$x>]!(1)
                    }

                    #[inline]
                    fn is_one(&self) -> bool {
                        *self == [<d$x>]!(1)
                    }
                }

                impl Zero for [<Decimal$x>] {
                    #[inline]
                    fn zero() -> Self {
                        [<d$x>]!(0)
                    }

                    #[inline]
                    fn is_zero(&self) -> bool {
                        [<Decimal$x>]::is_zero(*self)
                    }
                }

                impl Inv for [<Decimal$x>] {
                    type Output = Self;

                    #[inline]
                    fn inv(self) -> Self::Output {
                        [<d$x>]!(1) / self
                    }
                }

                forward_ref_unop!(impl Inv, inv for [<Decimal$x>]);

                impl MulAdd for [<Decimal$x>] {
                    type Output = Self;

                    #[inline]
                    fn mul_add(self, a: Self, b: Self) -> Self {
                        self.mul_add(a, b)
                    }
                }

                impl MulAddAssign for [<Decimal$x>] {
                    #[inline]
                    fn mul_add_assign(&mut self, a: Self, b: Self) {
                        *self = self.mul_add(a, b)
                    }
                }

                impl Pow<Self> for [<Decimal$x>] {
                    type Output = Self;

                    #[inline]
                    fn pow(self, rhs: Self) -> Self {
                        self.powf(rhs)
                    }
                }

                forward_ref_binop!(impl Pow, pow for [<Decimal$x>], [<Decimal$x>]);

                impl Pow<i32> for [<Decimal$x>] {
                    type Output = Self;

                    #[inline]
                    fn pow(self, rhs: i32) -> Self {
                        self.powi(rhs)
                    }
                }

                forward_ref_binop!(impl Pow, pow for [<Decimal$x>], i32);

                impl Num for [<Decimal$x>] {
                    type FromStrRadixErr = UnsupportedRadixError;

                    #[inline]
                    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                        if radix != 10 {
                            return Err(UnsupportedRadixError);
                        }

                        Ok([<Decimal$x>]::from_str(str).unwrap())
                    }
                }

                impl Signed for [<Decimal$x>] {
                    #[inline]
                    fn abs(&self) -> Self {
                        [<Decimal$x>]::abs(*self)
                    }

                    #[inline]
                    fn abs_sub(&self, other: &Self) -> Self {
                        #[allow(deprecated)]
                        [<Decimal$x>]::abs_sub(*self, *other)
                    }

                    #[inline]
                    fn signum(&self) -> Self {
                        [<Decimal$x>]::signum(*self)
                    }

                    #[inline]
                    fn is_positive(&self) -> bool {
                        [<Decimal$x>]::is_sign_positive(*self)
                    }

                    #[inline]
                    fn is_negative(&self) -> bool {
                        [<Decimal$x>]::is_sign_negative(*self)
                    }
                }
            };

            #[cfg(feature = "number_prefix")]
            impl number_prefix::Amounts for [<Decimal$x>] {
                const NUM_1000: Self = [<d$x>]!(1000);
                const NUM_1024: Self = [<d$x>]!(1024);

                fn is_negative(self) -> bool {
                    self.is_sign_negative()
                }
            }

            #[cfg(feature = "option-operations")]
            impl option_operations::OptionOperations for [<Decimal$x>] {}

            #[cfg(feature = "ord_subset")]
            impl ord_subset::OrdSubset for [<Decimal$x>] {
                fn is_outside_order(&self) -> bool {
                    self.is_nan()
                }
            }

            // FIXME make more NANs?
            #[cfg(feature = "quickcheck")]
            impl quickcheck::Arbitrary for [<Decimal$x>] {
                fn arbitrary(g: &mut quickcheck::Gen) -> Self {
                    let int: [<u$x>] = quickcheck::Arbitrary::arbitrary(g);
                    Self::from_bits(int)
                }
            }

            // FIXME rand_distr, review the strategy
            #[cfg(feature = "rand")]
            const _: () = {
                use rand::{prelude::*, distributions::*};

                // 1/10th of EPSILON -> step down instead of up
                const RNG_EXP: [<Decimal$x>] = per_width!($x, d32!(1E-7), d64!(1E-16), d128!(1E-34));

                impl Distribution<[<Decimal$x>]> for Standard {
                    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> [<Decimal$x>] {
                        // First we generate some [<Decimal$x>]::DIGITS digits for the significand.
                        const RANGE_TOP: [<u$x>] = [<u$x>]::pow(10, [<Decimal$x>]::DIGITS);
                        let digits = rng.gen_range(0..RANGE_TOP);

                        // Next we muliptly that by 10^(-[<Decimal$x>]::DIGITS) to get a range from [0, 1).
                        let digits_dec = [<Decimal$x>]::from_int(digits);

                        digits_dec * RNG_EXP
                    }
                }

                impl Distribution<[<Decimal$x>]> for OpenClosed01 {
                    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> [<Decimal$x>] {
                        // First we generate some [<Decimal$x>]::DIGITS digits for the significand.
                        const RANGE_TOP: [<u$x>] = [<u$x>]::pow(10, [<Decimal$x>]::DIGITS);
                        let digits = rng.gen_range(1..=RANGE_TOP);

                        // Next we muliptly that by 10^(-[<Decimal$x>]::DIGITS) to get a range from [0, 1).
                        let digits_dec = [<Decimal$x>]::from_int(digits);

                        digits_dec * RNG_EXP
                    }
                }

                impl Distribution<[<Decimal$x>]> for Open01 {
                    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> [<Decimal$x>] {
                        // First we generate some [<Decimal$x>]::DIGITS digits for the significand.
                        const RANGE_TOP: [<u$x>] = [<u$x>]::pow(10, [<Decimal$x>]::DIGITS);
                        let digits = rng.gen_range(1..RANGE_TOP);

                        // Next we muliptly that by 10^(-[<Decimal$x>]::DIGITS) to get a range from [0, 1).
                        let digits_dec = [<Decimal$x>]::from_int(digits);

                        digits_dec * RNG_EXP
                    }
                }

                // FIXME UniformFloat, UniformSampler
            };

            #[cfg(feature = "rkyv")]
            const _: () = {
                impl rkyv::Archive for [<Decimal$x>] {
                    type Archived =  Self;
                    type Resolver = ();

                    #[inline]
                    unsafe fn resolve(&self, _: usize, _: Self::Resolver, out: *mut Self::Archived) {
                        unsafe { out.write(*self) };
                    }
                }


                impl<S: rkyv::Fallible + ?Sized> rkyv::Serialize<S> for [<Decimal$x>] {
                    #[inline]
                    fn serialize(&self, _: &mut S) -> Result<Self::Resolver, S::Error> {
                        Ok(())
                    }
                }

                impl<D: rkyv::Fallible + ?Sized> rkyv::Deserialize<[<Decimal$x>], D> for rkyv::Archived<[<Decimal$x>]> {
                    #[inline]
                    fn deserialize(&self, _: &mut D) -> Result<[<Decimal$x>], D::Error> {
                        Ok(*self)
                    }
                }
            };

            #[cfg(feature = "rocket")]
            const _: () = {
                use rocket::{form, http::uri::fmt};

                impl<'v> form::FromFormField<'v> for [<Decimal$x>] {
                    #[inline]
                    fn from_value(field: form::ValueField<'v>) -> form::Result<'v, Self> {
                        field.value.parse().map_err(|_| form::Error::validation("not a valid number").into())
                    }
                }

                impl<P: fmt::Part> fmt::UriDisplay<P> for [<Decimal$x>]  {
                    #[inline]
                    fn fmt(&self, f: &mut fmt::Formatter<'_, P>) -> core::fmt::Result {
                        use core::fmt::Write;

                        let string: String = self.to_string().split('+').collect();
                        write!(f, "{}", string)
                    }
                }

                rocket::http::impl_from_uri_param_identity! { [<Decimal$x>] }

                impl<'a> rocket::request::FromParam<'a> for [<Decimal$x>] {
                    type Error = &'a str;

                    #[inline(always)]
                    fn from_param(param: &'a str) -> Result<Self, Self::Error> {
                        <[<Decimal$x>] as FromStr>::from_str(param).map_err(|_| param)
                    }
                }
            };

            #[cfg(feature = "rug")]
            const _: () = {
                use num_traits::Pow;
                use rug::{Assign, ops::{AddFrom, DivFrom, MulFrom, NegAssign, PowAssign, PowFrom, RemFrom, SubFrom}};

                impl Assign for [<Decimal$x>] {
                    #[inline]
                    fn assign(&mut self, src: Self) {
                        *self = src;
                    }
                }

                forward_ref_op_assign!(impl Assign, assign for [<Decimal$x>], [<Decimal$x>]);

                impl NegAssign for [<Decimal$x>] {
                    #[inline]
                    fn neg_assign(&mut self) {
                        *self = -*self;
                    }
                }

                impl PowAssign<i32> for [<Decimal$x>] {
                    #[inline]
                    fn pow_assign(&mut self, rhs: i32) {
                        *self = self.powi(rhs);
                    }
                }

                forward_ref_op_assign!(impl PowAssign, pow_assign for [<Decimal$x>], i32);

                impl PowAssign<[<Decimal$x>]> for [<Decimal$x>] {
                    #[inline]
                    fn pow_assign(&mut self, rhs: [<Decimal$x>]) {
                        *self = self.powf(rhs);
                    }
                }

                forward_ref_op_assign!(impl PowAssign, pow_assign for [<Decimal$x>], [<Decimal$x>]);

                rug_assign_from! { [<Decimal$x>]; add; AddFrom add_from }
                rug_assign_from! { [<Decimal$x>]; sub; SubFrom sub_from }
                rug_assign_from! { [<Decimal$x>]; mul; MulFrom mul_from }
                rug_assign_from! { [<Decimal$x>]; div; DivFrom div_from }
                rug_assign_from! { [<Decimal$x>]; rem; RemFrom rem_from }
                rug_assign_from! { [<Decimal$x>]; pow; PowFrom pow_from }

                // FIXME lots more to do
            };

            #[cfg(feature = "rusqlite")]
            const _: () = {
                impl From<[<Decimal$x>]> for rusqlite::types::Value {
                    /// `NaN`s are converted to `Null`,
                    /// infinities are converted to `double` infinities,
                    /// and finite values are converted to strings
                    /// which are compatible with SQLite's
                    /// [decimal.c extension](https://www.sqlite.org/floatingpoint.html#the_decimal_c_extension).
                    #[inline]
                    fn from(t: [<Decimal$x>]) -> Self {
                        if t.is_nan() {
                            rusqlite::types::Value::Null
                        } else if t.is_infinite() {
                            rusqlite::types::Value::Real(if t.is_sign_positive() { f64::INFINITY } else { f64::NEG_INFINITY })
                        } else {
                            rusqlite::types::Value::Text(t.to_string())
                        }
                    }
                }

                impl From<[<Decimal$x>]> for rusqlite::types::ToSqlOutput<'_> {
                    /// `NaN`s are converted to `Null`,
                    /// infinities are converted to `double` infinities,
                    /// and finite values are converted to strings
                    /// which are compatible with SQLite's
                    /// [decimal.c extension](https://www.sqlite.org/floatingpoint.html#the_decimal_c_extension).
                    #[inline]
                    fn from(t: [<Decimal$x>]) -> Self {
                        rusqlite::types::ToSqlOutput::Owned(t.into())
                    }
                }

                #[allow(clippy::doc_markdown)]
                impl rusqlite::ToSql for [<Decimal$x>] {
                    /// `NaN`s are converted to `Null`,
                    /// infinities are converted to `double` infinities,
                    /// and finite values are converted to strings
                    /// which are compatible with SQLite's
                    /// [decimal.c extension](https://www.sqlite.org/floatingpoint.html#the_decimal_c_extension).
                    #[inline]
                    fn to_sql(&self) -> Result<rusqlite::types::ToSqlOutput<'_>, rusqlite::Error> {
                        Ok(rusqlite::types::ToSqlOutput::from(*self))
                    }
                }

                impl rusqlite::types::FromSql for [<Decimal$x>] {
                    /// `Null`s are converted to `NaN`,
                    /// integers and doubles are converrted to `[<Decimal$x>]`s
                    /// (with `roundTiesToEven`),
                    /// and strings are parsed into decimals.
                    #[inline]
                    fn column_result(value: rusqlite::types::ValueRef<'_>) -> rusqlite::types::FromSqlResult<Self> {
                        match value {
                            rusqlite::types::ValueRef::Null => Ok([<Decimal$x>]::NAN),
                            rusqlite::types::ValueRef::Real(f) => Ok(Context::new().convert_format(f)),
                            rusqlite::types::ValueRef::Integer(i) => Ok([<Decimal$x>]::from_int(i)),
                            rusqlite::types::ValueRef::Text(t) => Ok({
                                match core::str::from_utf8(t) {
                                    Ok(s) => [<Decimal$x>]::from_str(s).unwrap(),
                                    Err(_) => [<Decimal$x>]::NAN,
                                }
                            }),
                            _ => Err(rusqlite::types::FromSqlError::InvalidType),
                        }
                    }
                }
            };

            #[cfg(feature = "rust_decimal")]
            const _: () = {
                impl TryFrom<[<Decimal$x>]> for rust_decimal::Decimal {
                    type Error = rust_decimal::Error;

                    fn try_from(value: [<Decimal$x>]) -> Result<Self, Self::Error> {
                        let result: Option<Self> = (|| {
                            // Can't convert NaN or infinity
                            if !value.is_finite() {
                                return None;
                            }

                            let (significand, mut exponent, signed) = value.integer_decode();
                            let mut significand = significand as u128;

                            // Decimal128 significand doesn't fit in 96 bits, need to ajust
                            only_128!($x,
                                // FIXME do this without looping

                                if significand.leading_zeros() < 32 { // Check if significand doesn't fit in 96 bits
                                    // Round ties away - FIXME round to even instead?
                                    significand = significand / 10 + (if significand % 10 >= 5 { 1 } else { 0 });
                                    exponent += 1;
                                    while significand.leading_zeros() < 32 {
                                        significand /= 10;
                                        exponent += 1;
                                    }
                                }
                            );

                            // rust_decimal stores its exponents as -28..=0
                            significand *= (10_u128).checked_pow(exponent.max(0) as u32)?;
                            exponent = exponent.min(0);

                            if exponent < -28 {
                                // Round ties away - FIXME round to even instead?
                                significand = significand / 10 + (if significand % 10 >= 5 { 1 } else { 0 });
                                exponent += 1;
                                // We already divided `significand` by 10 above, so we know that `significand < u128::MAX`.
                                // Therefore, if the `saturating_pow` saturates to `u128::MAX`,
                                // the result of the division will be 0.
                                significand /= (10_u128).saturating_pow((-28 - exponent).max(0) as u32);
                                exponent = -28;
                            }

                            // Max significand width is 96 bits
                            if significand.leading_zeros() < 32 {
                                return None;
                            }

                            let significand_bytes = (significand as u128).to_le_bytes();

                            let result: [u8; 16] = [
                                // Bits 0-15: unused
                                0,
                                0,
                                // Bits 16-23: exponent
                                -exponent as u8,
                                // Bits 24-30: unused,
                                // Bit 31: the sign of the Decimal value, 0 meaning positive and 1 meaning negative.
                                if signed { 128 } else { 0 },
                                // 96 bits of significand, low to high
                                significand_bytes[0],
                                significand_bytes[1],
                                significand_bytes[2],
                                significand_bytes[3],
                                significand_bytes[4],
                                significand_bytes[5],
                                significand_bytes[6],
                                significand_bytes[7],
                                significand_bytes[8],
                                significand_bytes[9],
                                significand_bytes[10],
                                significand_bytes[11],
                            ];

                            Some(rust_decimal::Decimal::deserialize(result))
                        })();

                        result.ok_or_else(|| rust_decimal::Error::from("Failed to convert"))
                    }
                }

                impl num_traits::Pow<[<Decimal$x>]> for rust_decimal::Decimal {
                    type Output = Self;

                    fn pow(self, rhs: [<Decimal$x>]) -> Self::Output {
                        <Self as rust_decimal::MathematicalOps>::powd(&self, Self::try_from(rhs).expect("Pow overflowed"))
                    }
                }

                // FIXME 32/64, don't go through string
                only_128!($x,
                    impl From<rust_decimal::Decimal> for [<Decimal$x>] {
                        fn from(d: rust_decimal::Decimal) -> Self {
                            Self::from_str(&d.to_string()).unwrap()
                        }
                    }
                );
            };

            #[cfg(feature = "safe-transmute")]
            const _: () = {
                unsafe impl safe_transmute::trivial::TriviallyTransmutable for [<Decimal$x>] {}
            };

            #[cfg(feature = "serde")]
            const _: () = {
                use serde::{de, ser};

                impl ser::Serialize for [<Decimal$x>] {
                    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
                    where
                        S: ser::Serializer,
                    {
                        serializer.serialize_str(&self.to_string())
                    }
                }

                impl<'de> de::Deserialize<'de> for [<Decimal$x>] {
                    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                    where
                        D: de::Deserializer<'de>,
                    {
                        struct [<Decimal$x Visitor>];

                        impl<'de> de::Visitor<'de> for [<Decimal$x Visitor>] {
                            type Value = [<Decimal$x>];

                            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                                formatter.write_str(stringify!([<Decimal$x>]))
                            }

                            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
                            where
                                E: de::Error,
                            {
                                Ok(Self::Value::from_str(v).unwrap())
                            }

                            // FICME non-string visitors
                        }

                        deserializer.deserialize_str([<Decimal$x Visitor>])
                    }
                }

                #[cfg(feature = "simba")]
                const _: () = {
                    impl simba::scalar::ComplexField for [<Decimal$x>] {
                        type RealField = Self;

                        #[inline]
                        fn from_real(re: Self::RealField) -> Self {
                            re
                        }

                        #[inline]
                        fn real(self) -> Self::RealField {
                            self
                        }

                        #[inline]
                        fn imaginary(self) -> Self::RealField {
                            [<d$x>]!(0)
                        }

                        #[inline]
                        fn norm1(self) -> Self::RealField {
                            self.abs()
                        }

                        #[inline]
                        fn modulus(self) -> Self::RealField {
                            self.abs()
                        }

                        #[inline]
                        fn modulus_squared(self) -> Self::RealField {
                            self * self
                        }

                        #[inline]
                        fn argument(self) -> Self::RealField {
                            if self >= [<d$x>]!(0) {
                                [<d$x>]!(0)
                            } else {
                                [<decimal$x>]::consts::PI
                            }
                        }

                        #[inline]
                        fn to_exp(self) -> (Self, Self) {
                            if self >= [<d$x>]!(0) {
                                (self, [<d$x>]!(1))
                            } else {
                                (-self, [<d$x>]!(-1))
                            }
                        }

                        trait_forward!($x, recip(self) -> Self);

                        #[inline]
                        fn conjugate(self) -> Self {
                            self
                        }

                        #[inline]
                        fn scale(self, factor: Self::RealField) -> Self {
                            self * factor
                        }

                        #[inline]
                        fn unscale(self, factor: Self::RealField) -> Self {
                            self / factor
                        }

                        trait_forward!($x, floor(self) -> Self);
                        trait_forward!($x, ceil(self) -> Self);
                        trait_forward!($x, round(self) -> Self);
                        trait_forward!($x, trunc(self) -> Self);
                        trait_forward!($x, fract(self) -> Self);
                        trait_forward!($x, abs(self) -> Self);
                        trait_forward!($x, signum(self) -> Self);
                        trait_forward!($x, mul_add(self, a: Self, b: Self) -> Self);
                        trait_forward!($x, powi(self, n: i32) -> Self);
                        trait_forward!($x, powf(self, n: Self) -> Self);
                        #[inline]
                        fn powc(self, n: Self) -> Self {
                            self.powf(n)
                        }
                        trait_forward!($x, sqrt(self) -> Self);

                        #[inline]
                        fn try_sqrt(self) -> Option<Self> {
                            if self >= [<d$x>]!(0) {
                                Some(self.sqrt())
                            } else {
                                None
                            }
                        }

                        trait_forward!($x, exp(self) -> Self);
                        trait_forward!($x, exp2(self) -> Self);
                        trait_forward!($x, exp_m1(self) -> Self);
                        trait_forward!($x, ln_1p(self) -> Self);
                        trait_forward!($x, ln(self) -> Self);
                        trait_forward!($x, log(self, base: Self) -> Self);
                        trait_forward!($x, log2(self) -> Self);
                        trait_forward!($x, log10(self) -> Self);
                        trait_forward!($x, cbrt(self) -> Self);
                        trait_forward!($x, hypot(self, other: Self) -> Self);
                        trait_forward!($x, sin(self) -> Self);
                        trait_forward!($x, cos(self) -> Self);
                        trait_forward!($x, tan(self) -> Self);
                        trait_forward!($x, asin(self) -> Self);
                        trait_forward!($x, acos(self) -> Self);
                        trait_forward!($x, atan(self) -> Self);
                        trait_forward!($x, sin_cos(self) -> (Self, Self));
                        trait_forward!($x, sinh(self) -> Self);
                        trait_forward!($x, cosh(self) -> Self);
                        trait_forward!($x, tanh(self) -> Self);
                        trait_forward!($x, asinh(self) -> Self);
                        trait_forward!($x, acosh(self) -> Self);
                        trait_forward!($x, atanh(self) -> Self);

                        #[inline]
                        fn is_finite(&self) -> bool {
                            [<Decimal$x>]::is_finite(*self)
                        }
                    }

                    impl simba::scalar::Field for [<Decimal$x>] {}

                    impl simba::scalar::RealField for [<Decimal$x>] {
                        #[inline]
                        fn is_sign_positive(&self) -> bool {
                            [<Decimal$x>]::is_sign_positive(*self)
                        }

                        #[inline]
                        fn is_sign_negative(&self) -> bool {
                            [<Decimal$x>]::is_sign_negative(*self)
                        }

                        trait_forward!($x, copysign(self, sign: Self) -> Self);
                        trait_forward!($x, max(self, other: Self) -> Self);
                        trait_forward!($x, min(self, other: Self) -> Self);
                        trait_forward!($x, clamp(self, min: Self, max: Self) -> Self);
                        trait_forward!($x, atan2(self, other: Self) -> Self);

                        #[inline]
                        fn min_value() -> Option<Self> {
                            Some([<Decimal$x>]::MIN)
                        }

                        #[inline]
                        fn max_value() -> Option<Self> {
                            Some([<Decimal$x>]::MAX)
                        }

                        trait_forward_const_math!($x, pi { PI });
                        trait_forward_const_math!($x, frac_pi_2 { FRAC_PI_2 });
                        trait_forward_const_math!($x, frac_pi_3 { FRAC_PI_3 });
                        trait_forward_const_math!($x, frac_pi_4 { FRAC_PI_4 });
                        trait_forward_const_math!($x, frac_pi_6 { FRAC_PI_6 });
                        trait_forward_const_math!($x, frac_pi_8 { FRAC_PI_8 });
                        trait_forward_const_math!($x, frac_1_pi { FRAC_1_PI });
                        trait_forward_const_math!($x, frac_2_pi { FRAC_2_PI });
                        trait_forward_const_math!($x, frac_2_sqrt_pi { FRAC_2_SQRT_PI });
                        trait_forward_const_math!($x, e { E });
                        trait_forward_const_math!($x, log2_e { LOG2_E });
                        trait_forward_const_math!($x, log10_e { LOG10_E });
                        trait_forward_const_math!($x, ln_2 { LN_2 });
                        trait_forward_const_math!($x, ln_10 { LN_10 });

                        #[inline]
                        fn two_pi() -> Self {
                            [<decimal$x>]::consts::TAU
                        }
                    }

                    impl simba::simd::PrimitiveSimdValue for [<Decimal$x>] {}

                    impl simba::simd::SimdValue for [<Decimal$x>] {
                        type Element = Self;
                        type SimdBool = bool;

                        #[inline]
                        fn lanes() -> usize {
                            1
                        }

                        #[inline]
                        fn splat(val: Self::Element) -> Self {
                            val
                        }

                        #[inline]
                        fn extract(&self, _: usize) -> Self::Element {
                            *self
                        }

                        #[inline]
                        unsafe fn extract_unchecked(&self, _: usize) -> Self::Element {
                            *self
                        }

                        #[inline]
                        fn replace(&mut self, _: usize, val: Self::Element) {
                            *self = val
                        }

                        #[inline]
                        unsafe fn replace_unchecked(&mut self, _: usize, val: Self::Element) {
                            *self = val
                        }

                        #[inline]
                        fn select(self, cond: Self::SimdBool, other: Self) -> Self {
                            if cond {
                                self
                            } else {
                                other
                            }
                        }
                    }
                };

                #[cfg(feature = "sprs")]
                const _: () = {
                    impl sprs::num_kinds::PrimitiveKind for [<Decimal$x>] {
                        fn num_kind() -> sprs::num_kinds::NumKind {
                            sprs::num_kinds::NumKind::Float
                        }
                    }
                };

                #[cfg(feature = "zerocopy")]
                const _: () = {
                    unsafe impl zerocopy::AsBytes for [<Decimal$x>] {
                        #[doc(hidden)]
                        fn only_derive_is_allowed_to_implement_this_trait() {}
                    }

                    unsafe impl zerocopy::FromBytes for [<Decimal$x>] {
                        #[doc(hidden)]
                        fn only_derive_is_allowed_to_implement_this_trait() {}
                    }
                };

                #[cfg(feature = "zeroize")]
                const _: () = {
                    impl zeroize::Zeroize for [<Decimal$x>] {
                        fn zeroize(&mut self) {
                            // SAFETY: `[<Decimal$x>]` has same size and alignment as itself
                            unsafe { core::ptr::write_volatile(self, Self::from_bits(0)) }
                            core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
                        }
                    }
                };
            };
        }
    )*};
}

decimal_impls!(32, 64, 128);

#[doc(hidden)]
pub use decimalfp_macros_support::{to_bits_128, to_bits_32, to_bits_64};

/// Allows writing [`Decimal32`] literals.
///
/// # Example
///
/// ```
/// use decimalfp::prelude::*;
///
/// const DEC = d32!(1.2345);
/// println!("{DEC}");
/// ```
#[macro_export]
macro_rules! d32 {
    ($lit:expr) => {
        $crate::Decimal32::from_bits($crate::to_bits_32!($lit))
    };
}

/// Allows writing [`Decimal64`] literals.
///
/// # Example
///
/// ```
/// use decimalfp::prelude::*;
///
/// const DEC = d64!(1.2342433245);
/// println!("{d}");
/// ```
#[macro_export]
macro_rules! d64 {
    ($lit:expr) => {
        $crate::Decimal64::from_bits($crate::to_bits_64!($lit))
    };
}

/// Allows writing [`Decimal128`] literals.
///
/// # Example
///
/// ```
/// use decimalfp::prelude::*;
///
/// const DEC = d128!(1.2342329243433245);
/// println!("{DEC}");
/// ```
#[macro_export]
macro_rules! d128 {
    ($lit:expr) => {
        $crate::Decimal128::from_bits($crate::to_bits_128!($lit))
    };
}

/// Contains the most commonly used elements of the library.
pub mod prelude {
    pub use crate::{d128, d32, d64, Decimal128, Decimal32, Decimal64};
}
