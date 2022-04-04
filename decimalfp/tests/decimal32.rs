// Adapted from rust-lang/rust/library/std/src//tests.rs

use core::num::FpCategory as Fp;
use decimalfp::decimal32::consts;
use decimalfp::prelude::*;
use decimalfp::*;

macro_rules! assert_approx_eq {
    ($a:expr, $b:expr) => {{
        let (a, b) = (&$a, &$b);
        assert!(
            (*a - *b).abs() <= d32!(1.0e-6),
            "{} is not approximately equal to {}",
            *a,
            *b
        );
    }};
}

#[test]
fn test_min_nan_32() {
    assert_eq!(Decimal32::NAN.min(d32!(2.0)), d32!(2.0));
    assert_eq!(d32!(2.0).min(Decimal32::NAN), d32!(2.0));
}

#[test]
fn test_max_nan_32() {
    assert_eq!(Decimal32::NAN.max(d32!(2.0)), d32!(2.0));
    assert_eq!(d32!(2.0).max(Decimal32::NAN), d32!(2.0));
}

#[test]
fn test_nan_32() {
    let nan: Decimal32 = Decimal32::NAN;
    assert!(nan.is_nan());
    assert!(!nan.is_infinite());
    assert!(!nan.is_finite());
    assert!(!nan.is_normal());
    assert!(nan.is_sign_positive());
    assert!(!nan.is_sign_negative());
    assert_eq!(Fp::Nan, nan.classify());
}

#[test]
fn test_infinity_32() {
    let inf: Decimal32 = Decimal32::INFINITY;
    assert!(inf.is_infinite());
    assert!(!inf.is_finite());
    assert!(inf.is_sign_positive());
    assert!(!inf.is_sign_negative());
    assert!(!inf.is_nan());
    assert!(!inf.is_normal());
    assert_eq!(Fp::Infinite, inf.classify());
}

#[test]
fn test_neg_infinity_32() {
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert!(neg_inf.is_infinite());
    assert!(!neg_inf.is_finite());
    assert!(!neg_inf.is_sign_positive());
    assert!(neg_inf.is_sign_negative());
    assert!(!neg_inf.is_nan());
    assert!(!neg_inf.is_normal());
    assert_eq!(Fp::Infinite, neg_inf.classify());
}

#[test]
fn test_zero_32() {
    let zero: Decimal32 = d32!(0.0);
    assert_eq!(d32!(0.0), zero);
    assert!(!zero.is_infinite());
    assert!(zero.is_finite());
    assert!(zero.is_sign_positive());
    assert!(!zero.is_sign_negative());
    assert!(!zero.is_nan());
    assert!(!zero.is_normal());
    assert_eq!(Fp::Zero, zero.classify());
}

#[test]
fn test_neg_zero_32() {
    let neg_zero: Decimal32 = d32!(-0.0);
    assert_eq!(d32!(0.0), neg_zero);
    assert!(!neg_zero.is_infinite());
    assert!(neg_zero.is_finite());
    assert!(!neg_zero.is_sign_positive());
    assert!(neg_zero.is_sign_negative());
    assert!(!neg_zero.is_nan());
    assert!(!neg_zero.is_normal());
    assert_eq!(Fp::Zero, neg_zero.classify());
}

#[test]
fn test_one_32() {
    let one: Decimal32 = d32!(1.0);
    assert_eq!(d32!(1.0), one);
    assert!(!one.is_infinite());
    assert!(one.is_finite());
    assert!(one.is_sign_positive());
    assert!(!one.is_sign_negative());
    assert!(!one.is_nan());
    assert!(one.is_normal());
    assert_eq!(Fp::Normal, one.classify());
}

#[test]
fn test_is_nan_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert!(nan.is_nan());
    assert!(!d32!(0.0).is_nan());
    assert!(!d32!(5.3).is_nan());
    assert!(!d32!(-10.732).is_nan());
    assert!(!inf.is_nan());
    assert!(!neg_inf.is_nan());
}

#[test]
fn test_is_infinite_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert!(!nan.is_infinite());
    assert!(inf.is_infinite());
    assert!(neg_inf.is_infinite());
    assert!(!d32!(0.0).is_infinite());
    assert!(!d32!(42.8).is_infinite());
    assert!(!d32!(-109.2).is_infinite());
}

#[test]
fn test_is_finite_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert!(!nan.is_finite());
    assert!(!inf.is_finite());
    assert!(!neg_inf.is_finite());
    assert!(d32!(0.0).is_finite());
    assert!(d32!(42.8).is_finite());
    assert!(d32!(-109.2).is_finite());
}

#[test]
fn test_is_normal_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    let zero: Decimal32 = d32!(0.0);
    let neg_zero: Decimal32 = d32!(-0.0);
    assert!(!nan.is_normal());
    assert!(!inf.is_normal());
    assert!(!neg_inf.is_normal());
    assert!(!zero.is_normal());
    assert!(!neg_zero.is_normal());
    assert!(d32!(1).is_normal());
    assert!(d32!(1e-95).is_normal());
    assert!(!d32!(1e-96).is_normal());
}

#[test]
fn test_classify_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    let zero: Decimal32 = d32!(0.0);
    let neg_zero: Decimal32 = d32!(-0.0);
    assert_eq!(nan.classify(), Fp::Nan);
    assert_eq!(inf.classify(), Fp::Infinite);
    assert_eq!(neg_inf.classify(), Fp::Infinite);
    assert_eq!(zero.classify(), Fp::Zero);
    assert_eq!(neg_zero.classify(), Fp::Zero);
    assert_eq!(d32!(1e-95).classify(), Fp::Normal);
    assert_eq!(d32!(1e-96).classify(), Fp::Subnormal);
}

#[test]
fn test_floor_32() {
    assert_approx_eq!(d32!(1.0).floor(), d32!(1.0));
    assert_approx_eq!(d32!(1.3).floor(), d32!(1.0));
    assert_approx_eq!(d32!(1.5).floor(), d32!(1.0));
    assert_approx_eq!(d32!(1.7).floor(), d32!(1.0));
    assert_approx_eq!(d32!(0.0).floor(), d32!(0.0));
    assert_approx_eq!(d32!(-0.0).floor(), d32!(-0.0));
    assert_approx_eq!(d32!(-1.0).floor(), d32!(-1.0));
    assert_approx_eq!(d32!(-1.3).floor(), d32!(-2.0));
    assert_approx_eq!(d32!(-1.5).floor(), d32!(-2.0));
    assert_approx_eq!(d32!(-1.7).floor(), d32!(-2.0));
}

#[test]
fn test_ceil_32() {
    assert_approx_eq!(d32!(1.0).ceil(), d32!(1.0));
    assert_approx_eq!(d32!(1.3).ceil(), d32!(2.0));
    assert_approx_eq!(d32!(1.5).ceil(), d32!(2.0));
    assert_approx_eq!(d32!(1.7).ceil(), d32!(2.0));
    assert_approx_eq!(d32!(0.0).ceil(), d32!(0.0));
    assert_approx_eq!(d32!(-0.0).ceil(), d32!(-0.0));
    assert_approx_eq!(d32!(-1.0).ceil(), d32!(-1.0));
    assert_approx_eq!(d32!(-1.3).ceil(), d32!(-1.0));
    assert_approx_eq!(d32!(-1.5).ceil(), d32!(-1.0));
    assert_approx_eq!(d32!(-1.7).ceil(), d32!(-1.0));
}

#[test]
fn test_round_32() {
    assert_approx_eq!(d32!(1.0).round(), d32!(1.0));
    assert_approx_eq!(d32!(1.3).round(), d32!(1.0));
    assert_approx_eq!(d32!(1.5).round(), d32!(2.0));
    assert_approx_eq!(d32!(1.7).round(), d32!(2.0));
    assert_approx_eq!(d32!(0.0).round(), d32!(0.0));
    assert_approx_eq!(d32!(-0.0).round(), d32!(-0.0));
    assert_approx_eq!(d32!(-1.0).round(), d32!(-1.0));
    assert_approx_eq!(d32!(-1.3).round(), d32!(-1.0));
    assert_approx_eq!(d32!(-1.5).round(), d32!(-2.0));
    assert_approx_eq!(d32!(-1.7).round(), d32!(-2.0));
}

#[test]
fn test_trunc_32() {
    assert_approx_eq!(d32!(1.0).trunc(), d32!(1.0));
    assert_approx_eq!(d32!(1.3).trunc(), d32!(1.0));
    assert_approx_eq!(d32!(1.5).trunc(), d32!(1.0));
    assert_approx_eq!(d32!(1.7).trunc(), d32!(1.0));
    assert_approx_eq!(d32!(0.0).trunc(), d32!(0.0));
    assert_approx_eq!(d32!(-0.0).trunc(), d32!(-0.0));
    assert_approx_eq!(d32!(-1.0).trunc(), d32!(-1.0));
    assert_approx_eq!(d32!(-1.3).trunc(), d32!(-1.0));
    assert_approx_eq!(d32!(-1.5).trunc(), d32!(-1.0));
    assert_approx_eq!(d32!(-1.7).trunc(), d32!(-1.0));
}

#[test]
fn test_fract_32() {
    assert_approx_eq!(d32!(1.0).fract(), d32!(0.0));
    assert_approx_eq!(d32!(1.3).fract(), d32!(0.3));
    assert_approx_eq!(d32!(1.5).fract(), d32!(0.5));
    assert_approx_eq!(d32!(1.7).fract(), d32!(0.7));
    assert_approx_eq!(d32!(0.0).fract(), d32!(0.0));
    assert_approx_eq!(d32!(-0.0).fract(), d32!(-0.0));
    assert_approx_eq!(d32!(-1.0).fract(), d32!(-0.0));
    assert_approx_eq!(d32!(-1.3).fract(), d32!(-0.3));
    assert_approx_eq!(d32!(-1.5).fract(), d32!(-0.5));
    assert_approx_eq!(d32!(-1.7).fract(), d32!(-0.7));
}

#[test]
fn test_abs_32() {
    assert_eq!(Decimal32::INFINITY.abs(), Decimal32::INFINITY);
    assert_eq!(d32!(1).abs(), d32!(1));
    assert_eq!(d32!(0).abs(), d32!(0));
    assert_eq!(d32!(-0).abs(), d32!(0));
    assert_eq!(d32!(-1).abs(), d32!(1));
    assert_eq!(Decimal32::NEG_INFINITY.abs(), Decimal32::INFINITY);
    assert_eq!((d32!(1) / Decimal32::NEG_INFINITY).abs(), d32!(0));
    assert!(Decimal32::NAN.abs().is_nan());
}

#[test]
fn test_signum_32() {
    assert_eq!(Decimal32::INFINITY.signum(), d32!(1));
    assert_eq!(d32!(1).signum(), d32!(1));
    assert_eq!(d32!(0).signum(), d32!(1));
    assert_eq!(d32!(-0).signum(), d32!(-1));
    assert_eq!(d32!(-1).signum(), d32!(-1));
    assert_eq!(Decimal32::NEG_INFINITY.signum(), d32!(-1));
    assert_eq!((d32!(1) / Decimal32::NEG_INFINITY).signum(), d32!(-1));
    assert!(Decimal32::NAN.signum().is_nan());
}

#[test]
fn test_is_sign_positive_32() {
    assert!(Decimal32::INFINITY.is_sign_positive());
    assert!(d32!(1).is_sign_positive());
    assert!(d32!(0).is_sign_positive());
    assert!(!d32!(-0).is_sign_positive());
    assert!(!d32!(-1).is_sign_positive());
    assert!(!Decimal32::NEG_INFINITY.is_sign_positive());
    assert!(!(d32!(1) / Decimal32::NEG_INFINITY).is_sign_positive());
    assert!(Decimal32::NAN.is_sign_positive());
    assert!(!(-Decimal32::NAN).is_sign_positive());
}

#[test]
fn test_is_sign_negative_32() {
    assert!(!Decimal32::INFINITY.is_sign_negative());
    assert!(!d32!(1).is_sign_negative());
    assert!(!d32!(0).is_sign_negative());
    assert!(d32!(-0).is_sign_negative());
    assert!(d32!(-1).is_sign_negative());
    assert!(Decimal32::NEG_INFINITY.is_sign_negative());
    assert!((d32!(1) / Decimal32::NEG_INFINITY).is_sign_negative());
    assert!(!Decimal32::NAN.is_sign_negative());
    assert!((-Decimal32::NAN).is_sign_negative());
}

#[test]
fn test_mul_add_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert_approx_eq!(d32!(12.3).mul_add(d32!(4.5), d32!(6.7)), d32!(62.05));
    assert_approx_eq!(d32!(-12.3).mul_add(d32!(-4.5), d32!(-6.7)), d32!(48.65));
    assert_approx_eq!(d32!(0.0).mul_add(d32!(8.9), d32!(1.2)), d32!(1.2));
    assert_approx_eq!(d32!(3.4).mul_add(d32!(-0.0), d32!(5.6)), d32!(5.6));
    assert!(nan.mul_add(d32!(7.8), d32!(9.0)).is_nan());
    assert_eq!(inf.mul_add(d32!(7.8), d32!(9.0)), inf);
    assert_eq!(neg_inf.mul_add(d32!(7.8), d32!(9.0)), neg_inf);
    assert_eq!(d32!(8.9).mul_add(inf, d32!(3.2)), inf);
    assert_eq!(d32!(-3.2).mul_add(d32!(2.4), neg_inf), neg_inf);
}

#[test]
fn test_recip_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert_eq!(d32!(1.0).recip(), d32!(1.0));
    assert_eq!(d32!(2.0).recip(), d32!(0.5));
    assert_eq!(d32!(-0.4).recip(), d32!(-2.5));
    assert_eq!(d32!(0.0).recip(), inf);
    assert!(nan.recip().is_nan());
    assert_eq!(inf.recip(), d32!(0.0));
    assert_eq!(neg_inf.recip(), d32!(0.0));
}

#[test]
fn test_powi_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert_eq!(d32!(1.0).powi(1), d32!(1.0));
    assert_approx_eq!(d32!(-3.1).powi(2), d32!(9.61));
    assert_approx_eq!(d32!(5.9).powi(-2), d32!(0.028727));
    assert_eq!(d32!(8.3).powi(0), d32!(1.0));
    assert!(nan.powi(2).is_nan());
    assert_eq!(inf.powi(3), inf);
    assert_eq!(neg_inf.powi(2), inf);
}

#[test]
fn test_powf_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert_eq!(d32!(1.0).powf(d32!(1.0)), d32!(1.0));
    assert_approx_eq!(d32!(3.4).powf(d32!(4.5)), d32!(246.408183));
    assert_approx_eq!(d32!(2.7).powf(d32!(-3.2)), d32!(0.041652));
    assert_approx_eq!(d32!(-3.1).powf(d32!(2.0)), d32!(9.61));
    assert_approx_eq!(d32!(5.9).powf(d32!(-2.0)), d32!(0.028727));
    assert_eq!(d32!(8.3).powf(d32!(0.0)), d32!(1.0));
    assert!(nan.powf(d32!(2.0)).is_nan());
    assert_eq!(inf.powf(d32!(2.0)), inf);
    assert_eq!(neg_inf.powf(d32!(3.0)), neg_inf);
}

#[test]
fn test_sqrt_domain_32() {
    assert!(Decimal32::NAN.sqrt().is_nan());
    assert!(Decimal32::NEG_INFINITY.sqrt().is_nan());
    assert!(d32!(-1.0).sqrt().is_nan());
    assert_eq!(d32!(-0.0).sqrt(), d32!(-0.0));
    assert_eq!(d32!(0.0).sqrt(), d32!(0.0));
    assert_eq!(d32!(1.0).sqrt(), d32!(1.0));
    assert_eq!(Decimal32::INFINITY.sqrt(), Decimal32::INFINITY);
}

#[test]
fn test_exp_32() {
    assert_eq!(d32!(1.0), d32!(0.0).exp());
    assert_approx_eq!(d32!(2.718282), d32!(1.0).exp());
    assert_approx_eq!(d32!(148.413159), d32!(5.0).exp());

    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    let nan: Decimal32 = Decimal32::NAN;
    assert_eq!(inf, inf.exp());
    assert_eq!(d32!(0.0), neg_inf.exp());
    assert!(nan.exp().is_nan());
}

#[test]
fn test_exp2_32() {
    assert_eq!(d32!(32.0), d32!(5.0).exp2());
    assert_eq!(d32!(1.0), d32!(0.0).exp2());

    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    let nan: Decimal32 = Decimal32::NAN;
    assert_eq!(inf, inf.exp2());
    assert_eq!(d32!(0.0), neg_inf.exp2());
    assert!(nan.exp2().is_nan());
}

#[test]
fn test_ln_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert_approx_eq!(d32!(1.0).exp().ln(), d32!(1.0));
    assert!(nan.ln().is_nan());
    assert_eq!(inf.ln(), inf);
    assert!(neg_inf.ln().is_nan());
    assert!(d32!(-2.3).ln().is_nan());
    assert_eq!(d32!(-0.0).ln(), neg_inf);
    assert_eq!(d32!(0.0).ln(), neg_inf);
    assert_approx_eq!(d32!(4.0).ln(), d32!(1.386294));
}

#[test]
fn test_log_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert_eq!(d32!(10.0).log(d32!(10.0)), d32!(1.0));
    assert_approx_eq!(d32!(2.3).log(d32!(3.5)), d32!(0.664858));
    assert_eq!(d32!(1.0).exp().log(d32!(1.0).exp()), d32!(1.0));
    assert!(d32!(1.0).log(d32!(1.0)).is_nan());
    assert!(d32!(1.0).log(d32!(-13.9)).is_nan());
    assert!(nan.log(d32!(2.3)).is_nan());
    assert_eq!(inf.log(d32!(10.0)), inf);
    assert!(neg_inf.log(d32!(8.8)).is_nan());
    assert!(d32!(-2.3).log(d32!(0.1)).is_nan());
    assert_eq!(d32!(-0.0).log(d32!(2.0)), neg_inf);
    assert_eq!(d32!(0.0).log(d32!(7.0)), neg_inf);
}

#[test]
fn test_log2_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert_approx_eq!(d32!(10.0).log2(), d32!(3.321928));
    assert_approx_eq!(d32!(2.3).log2(), d32!(1.201634));
    assert_approx_eq!(d32!(1.0).exp().log2(), d32!(1.442695));
    assert!(nan.log2().is_nan());
    assert_eq!(inf.log2(), inf);
    assert!(neg_inf.log2().is_nan());
    assert!(d32!(-2.3).log2().is_nan());
    assert_eq!(d32!(-0.0).log2(), neg_inf);
    assert_eq!(d32!(0.0).log2(), neg_inf);
}

#[test]
fn test_log10_32() {
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert_eq!(d32!(10.0).log10(), d32!(1.0));
    assert_approx_eq!(d32!(2.3).log10(), d32!(0.361728));
    assert_approx_eq!(d32!(1.0).exp().log10(), d32!(0.434294));
    assert_eq!(d32!(1.0).log10(), d32!(0.0));
    assert!(nan.log10().is_nan());
    assert_eq!(inf.log10(), inf);
    assert!(neg_inf.log10().is_nan());
    assert!(d32!(-2.3).log10().is_nan());
    assert_eq!(d32!(-0.0).log10(), neg_inf);
    assert_eq!(d32!(0.0).log10(), neg_inf);
}

#[test]
fn test_to_degrees_32() {
    let pi: Decimal32 = consts::PI;
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert_eq!(d32!(0.0).to_degrees(), d32!(0.0));
    assert_approx_eq!(d32!(-5.8).to_degrees(), d32!(-332.315521));
    assert_eq!(pi.to_degrees(), d32!(180.0));
    assert!(nan.to_degrees().is_nan());
    assert_eq!(inf.to_degrees(), inf);
    assert_eq!(neg_inf.to_degrees(), neg_inf);
}

#[test]
fn test_to_radians_32() {
    let pi: Decimal32 = consts::PI;
    let nan: Decimal32 = Decimal32::NAN;
    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    assert_eq!(d32!(0.0).to_radians(), d32!(0.0));
    assert_approx_eq!(d32!(154.6).to_radians(), d32!(2.698279));
    assert_approx_eq!(d32!(-332.31).to_radians(), d32!(-5.799903));
    assert_approx_eq!(d32!(180.0).to_radians(), pi);
    assert!(nan.to_radians().is_nan());
    assert_eq!(inf.to_radians(), inf);
    assert_eq!(neg_inf.to_radians(), neg_inf);
}

#[test]
fn test_asinh_32() {
    assert_eq!(d32!(0.0).asinh(), d32!(0.0));
    assert_eq!(d32!(-0.0).asinh(), d32!(-0.0));

    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    let nan: Decimal32 = Decimal32::NAN;
    assert_eq!(inf.asinh(), inf);
    assert_eq!(neg_inf.asinh(), neg_inf);
    assert!(nan.asinh().is_nan());
    assert!(d32!(-0.0).asinh().is_sign_negative());
    // issue 63271
    assert_approx_eq!(d32!(2.0).asinh(), d32!(1.443635475178810342493276740273105));
    assert_approx_eq!(
        d32!(-2.0).asinh(),
        d32!(-1.443635475178810342493276740273105)
    );
    // regression test for the catastrophic cancellation fixed in 72486
    assert_approx_eq!(
        d32!(-67452098.07139316).asinh(),
        d32!(-18.72007542627454439398548429400083)
    );
}

#[test]
fn test_acosh_32() {
    assert_eq!(d32!(1.0).acosh(), d32!(0.0));
    assert!(d32!(0.999).acosh().is_nan());

    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    let nan: Decimal32 = Decimal32::NAN;
    assert_eq!(inf.acosh(), inf);
    assert!(neg_inf.acosh().is_nan());
    assert!(nan.acosh().is_nan());
    assert_approx_eq!(
        d32!(2.0).acosh(),
        d32!(1.31695789692481670862504634730796844)
    );
    assert_approx_eq!(
        d32!(3.0).acosh(),
        d32!(1.76274717403908605046521864995958461)
    );
}

#[test]
fn test_atanh_32() {
    assert_eq!(d32!(0.0).atanh(), d32!(0.0));
    assert_eq!(d32!(-0.0).atanh(), d32!(-0.0));

    let inf: Decimal32 = Decimal32::INFINITY;
    let neg_inf: Decimal32 = Decimal32::NEG_INFINITY;
    let nan: Decimal32 = Decimal32::NAN;
    assert_eq!(d32!(1.0).atanh(), inf);
    assert_eq!(d32!(-1.0).atanh(), neg_inf);
    assert!(d32!(2).atanh().atanh().is_nan());
    assert!(d32!(-2).atanh().atanh().is_nan());
    assert!(inf.atanh().is_nan());
    assert!(neg_inf.atanh().is_nan());
    assert!(nan.atanh().is_nan());
    assert_approx_eq!(
        d32!(0.5).atanh(),
        d32!(0.54930614433405484569762261846126285)
    );
    assert_approx_eq!(
        d32!(-0.5).atanh(),
        d32!(-0.54930614433405484569762261846126285)
    );
}

#[test]
fn test_real_consts_32() {
    use decimal32::consts;
    let pi: Decimal32 = consts::PI;
    let frac_pi_2: Decimal32 = consts::FRAC_PI_2;
    let frac_pi_3: Decimal32 = consts::FRAC_PI_3;
    let frac_pi_4: Decimal32 = consts::FRAC_PI_4;
    let frac_pi_6: Decimal32 = consts::FRAC_PI_6;
    let frac_pi_8: Decimal32 = consts::FRAC_PI_8;
    let frac_1_pi: Decimal32 = consts::FRAC_1_PI;
    let frac_2_pi: Decimal32 = consts::FRAC_2_PI;
    let frac_2_sqrtpi: Decimal32 = consts::FRAC_2_SQRT_PI;
    let sqrt2: Decimal32 = consts::SQRT_2;
    let frac_1_sqrt2: Decimal32 = consts::FRAC_1_SQRT_2;
    let e: Decimal32 = consts::E;
    let log2_e: Decimal32 = consts::LOG2_E;
    let log10_e: Decimal32 = consts::LOG10_E;
    let ln_2: Decimal32 = consts::LN_2;
    let ln_10: Decimal32 = consts::LN_10;

    assert_approx_eq!(frac_pi_2, pi / d32!(2));
    assert_approx_eq!(frac_pi_3, pi / d32!(3));
    assert_approx_eq!(frac_pi_4, pi / d32!(4));
    assert_approx_eq!(frac_pi_6, pi / d32!(6));
    assert_approx_eq!(frac_pi_8, pi / d32!(8));
    assert_approx_eq!(frac_1_pi, d32!(1) / pi);
    assert_approx_eq!(frac_2_pi, d32!(2) / pi);
    assert_approx_eq!(frac_2_sqrtpi, d32!(2) / pi.sqrt());
    assert_approx_eq!(sqrt2, d32!(2).sqrt());
    assert_approx_eq!(frac_1_sqrt2, d32!(1) / d32!(2).sqrt());
    assert_approx_eq!(log2_e, e.log2());
    assert_approx_eq!(log10_e, e.log10());
    assert_approx_eq!(ln_2, d32!(2).ln());
    assert_approx_eq!(ln_10, d32!(10).ln());
}

#[test]
fn test_float_bits_conv_32() {
    assert_eq!(d32!(1).to_bits(), 0x32800001);
    assert_eq!(d32!(12.5).to_bits(), 0x3200007d);
    assert_eq!(d32!(1337).to_bits(), 0x32800539);
    assert_eq!(d32!(-14.25).to_bits(), 0xb1800591);
    assert_eq!(Decimal32::from_bits(0x32800001), d32!(1.0));
    assert_eq!(Decimal32::from_bits(0x3200007d), d32!(12.5));
    assert_eq!(Decimal32::from_bits(0x32800539), d32!(1337.0));
    assert_eq!(Decimal32::from_bits(0xb1800591), d32!(-14.25));

    // Check that NaNs roundtrip their bits regardless of signaling-ness
    // 0xA is 0b1010; 0x5 is 0b0101 -- so these two together clobbers all the mantissa bits
    let masked_nan1 = Decimal32::NAN.to_bits() ^ 0x00AA_AAAA;
    let masked_nan2 = Decimal32::NAN.to_bits() ^ 0x0055_5555;
    assert!(Decimal32::from_bits(masked_nan1).is_nan());
    assert!(Decimal32::from_bits(masked_nan2).is_nan());

    assert_eq!(Decimal32::from_bits(masked_nan1).to_bits(), masked_nan1);
    assert_eq!(Decimal32::from_bits(masked_nan2).to_bits(), masked_nan2);
}

#[test]
#[should_panic]
fn test_clamp_min_greater_than_max_32() {
    let _ = d32!(1.0).clamp(d32!(3.0), d32!(1.0));
}

#[test]
#[should_panic]
fn test_clamp_min_is_nan_32() {
    let _ = d32!(1.0).clamp(Decimal32::NAN, d32!(1.0));
}

#[test]
#[should_panic]
fn test_clamp_max_is_nan_32() {
    let _ = d32!(1.0).clamp(d32!(3.0), Decimal32::NAN);
}

#[test]
fn test_total_cmp_32() {
    use core::cmp::Ordering;

    fn min_subnorm() -> Decimal32 {
        Decimal32::MIN_POSITIVE
            / Decimal32::powf(
                d32!(10.0),
                Decimal32::from_int(Decimal32::MANTISSA_DIGITS) - d32!(1.0),
            )
    }

    fn max_subnorm() -> Decimal32 {
        Decimal32::MIN_POSITIVE - min_subnorm()
    }

    fn q_nan() -> Decimal32 {
        Decimal32::NAN
    }

    fn s_nan() -> Decimal32 {
        Decimal32::SNAN
    }

    assert_eq!(Ordering::Equal, (-q_nan()).total_cmp(&-q_nan()));
    assert_eq!(Ordering::Equal, (-s_nan()).total_cmp(&-s_nan()));
    assert_eq!(
        Ordering::Equal,
        (-Decimal32::INFINITY).total_cmp(&-Decimal32::INFINITY)
    );
    assert_eq!(
        Ordering::Equal,
        (-Decimal32::MAX).total_cmp(&-Decimal32::MAX)
    );
    assert_eq!(Ordering::Equal, d32!(-2.5).total_cmp(&d32!(-2.5)));
    assert_eq!(Ordering::Equal, d32!(-1.0).total_cmp(&d32!(-1.0)));
    assert_eq!(Ordering::Equal, d32!(-1.5).total_cmp(&d32!(-1.5)));
    assert_eq!(Ordering::Equal, d32!(-0.5).total_cmp(&d32!(-0.5)));
    assert_eq!(
        Ordering::Equal,
        (-Decimal32::MIN_POSITIVE).total_cmp(&-Decimal32::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Equal, (-max_subnorm()).total_cmp(&-max_subnorm()));
    assert_eq!(Ordering::Equal, (-min_subnorm()).total_cmp(&-min_subnorm()));
    assert_eq!(Ordering::Equal, d32!(-0.0).total_cmp(&d32!(-0.0)));
    assert_eq!(Ordering::Equal, d32!(0.0).total_cmp(&d32!(0.0)));
    assert_eq!(Ordering::Equal, min_subnorm().total_cmp(&min_subnorm()));
    assert_eq!(Ordering::Equal, max_subnorm().total_cmp(&max_subnorm()));
    assert_eq!(
        Ordering::Equal,
        Decimal32::MIN_POSITIVE.total_cmp(&Decimal32::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Equal, d32!(0.5).total_cmp(&d32!(0.5)));
    assert_eq!(Ordering::Equal, d32!(1.0).total_cmp(&d32!(1.0)));
    assert_eq!(Ordering::Equal, d32!(1.5).total_cmp(&d32!(1.5)));
    assert_eq!(Ordering::Equal, d32!(2.5).total_cmp(&d32!(2.5)));
    assert_eq!(Ordering::Equal, Decimal32::MAX.total_cmp(&Decimal32::MAX));
    assert_eq!(
        Ordering::Equal,
        Decimal32::INFINITY.total_cmp(&Decimal32::INFINITY)
    );
    assert_eq!(Ordering::Equal, s_nan().total_cmp(&s_nan()));
    assert_eq!(Ordering::Equal, q_nan().total_cmp(&q_nan()));

    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-s_nan()));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&-Decimal32::INFINITY));
    assert_eq!(
        Ordering::Less,
        (-Decimal32::INFINITY).total_cmp(&-Decimal32::MAX)
    );
    assert_eq!(Ordering::Less, (-Decimal32::MAX).total_cmp(&d32!(-2.5)));
    assert_eq!(Ordering::Less, d32!(-2.5).total_cmp(&d32!(-1.5)));
    assert_eq!(Ordering::Less, d32!(-1.5).total_cmp(&d32!(-1.0)));
    assert_eq!(Ordering::Less, d32!(-1.0).total_cmp(&d32!(-0.5)));
    assert_eq!(
        Ordering::Less,
        d32!(-0.5).total_cmp(&-Decimal32::MIN_POSITIVE)
    );
    assert_eq!(
        Ordering::Less,
        (-Decimal32::MIN_POSITIVE).total_cmp(&-max_subnorm())
    );
    assert_eq!(Ordering::Less, (-max_subnorm()).total_cmp(&-min_subnorm()));
    assert_eq!(Ordering::Less, (-min_subnorm()).total_cmp(&d32!(-0.0)));
    assert_eq!(Ordering::Less, d32!(-0.0).total_cmp(&d32!(0.0)));
    assert_eq!(Ordering::Less, d32!(0.0).total_cmp(&min_subnorm()));
    assert_eq!(Ordering::Less, min_subnorm().total_cmp(&max_subnorm()));
    assert_eq!(
        Ordering::Less,
        max_subnorm().total_cmp(&Decimal32::MIN_POSITIVE)
    );
    assert_eq!(
        Ordering::Less,
        Decimal32::MIN_POSITIVE.total_cmp(&d32!(0.5))
    );
    assert_eq!(Ordering::Less, d32!(0.5).total_cmp(&d32!(1.0)));
    assert_eq!(Ordering::Less, d32!(1.0).total_cmp(&d32!(1.5)));
    assert_eq!(Ordering::Less, d32!(1.5).total_cmp(&d32!(2.5)));
    assert_eq!(Ordering::Less, d32!(2.5).total_cmp(&Decimal32::MAX));
    assert_eq!(
        Ordering::Less,
        Decimal32::MAX.total_cmp(&Decimal32::INFINITY)
    );
    assert_eq!(Ordering::Less, Decimal32::INFINITY.total_cmp(&s_nan()));
    assert_eq!(Ordering::Less, s_nan().total_cmp(&q_nan()));

    assert_eq!(Ordering::Greater, (-s_nan()).total_cmp(&-q_nan()));
    assert_eq!(
        Ordering::Greater,
        (-Decimal32::INFINITY).total_cmp(&-s_nan())
    );
    assert_eq!(
        Ordering::Greater,
        (-Decimal32::MAX).total_cmp(&-Decimal32::INFINITY)
    );
    assert_eq!(Ordering::Greater, d32!(-2.5).total_cmp(&-Decimal32::MAX));
    assert_eq!(Ordering::Greater, d32!(-1.5).total_cmp(&d32!(-2.5)));
    assert_eq!(Ordering::Greater, d32!(-1.0).total_cmp(&d32!(-1.5)));
    assert_eq!(Ordering::Greater, d32!(-0.5).total_cmp(&d32!(-1.0)));
    assert_eq!(
        Ordering::Greater,
        (-Decimal32::MIN_POSITIVE).total_cmp(&d32!(-0.5))
    );
    assert_eq!(
        Ordering::Greater,
        (-max_subnorm()).total_cmp(&-Decimal32::MIN_POSITIVE)
    );
    assert_eq!(
        Ordering::Greater,
        (-min_subnorm()).total_cmp(&-max_subnorm())
    );
    assert_eq!(Ordering::Greater, d32!(-0.0).total_cmp(&-min_subnorm()));
    assert_eq!(Ordering::Greater, d32!(0.0).total_cmp(&d32!(-0.0)));
    assert_eq!(Ordering::Greater, min_subnorm().total_cmp(&d32!(0.0)));
    assert_eq!(Ordering::Greater, max_subnorm().total_cmp(&min_subnorm()));
    assert_eq!(
        Ordering::Greater,
        Decimal32::MIN_POSITIVE.total_cmp(&max_subnorm())
    );
    assert_eq!(
        Ordering::Greater,
        d32!(0.5).total_cmp(&Decimal32::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Greater, d32!(1.0).total_cmp(&d32!(0.5)));
    assert_eq!(Ordering::Greater, d32!(1.5).total_cmp(&d32!(1.0)));
    assert_eq!(Ordering::Greater, d32!(2.5).total_cmp(&d32!(1.5)));
    assert_eq!(Ordering::Greater, Decimal32::MAX.total_cmp(&d32!(2.5)));
    assert_eq!(
        Ordering::Greater,
        Decimal32::INFINITY.total_cmp(&Decimal32::MAX)
    );
    assert_eq!(Ordering::Greater, s_nan().total_cmp(&Decimal32::INFINITY));
    assert_eq!(Ordering::Greater, q_nan().total_cmp(&s_nan()));

    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-s_nan()));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-Decimal32::INFINITY));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-Decimal32::MAX));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d32!(-2.5)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d32!(-1.5)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d32!(-1.0)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d32!(-0.5)));
    assert_eq!(
        Ordering::Less,
        (-q_nan()).total_cmp(&-Decimal32::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-max_subnorm()));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-min_subnorm()));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d32!(-0.0)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d32!(0.0)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&min_subnorm()));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&max_subnorm()));
    assert_eq!(
        Ordering::Less,
        (-q_nan()).total_cmp(&Decimal32::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d32!(0.5)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d32!(1.0)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d32!(1.5)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d32!(2.5)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&Decimal32::MAX));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&Decimal32::INFINITY));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&s_nan()));

    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&-Decimal32::INFINITY));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&-Decimal32::MAX));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d32!(-2.5)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d32!(-1.5)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d32!(-1.0)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d32!(-0.5)));
    assert_eq!(
        Ordering::Less,
        (-s_nan()).total_cmp(&-Decimal32::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&-max_subnorm()));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&-min_subnorm()));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d32!(-0.0)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d32!(0.0)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&min_subnorm()));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&max_subnorm()));
    assert_eq!(
        Ordering::Less,
        (-s_nan()).total_cmp(&Decimal32::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d32!(0.5)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d32!(1.0)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d32!(1.5)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d32!(2.5)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&Decimal32::MAX));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&Decimal32::INFINITY));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&s_nan()));
}
