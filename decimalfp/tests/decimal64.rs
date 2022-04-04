// Adapted from rust-lang/rust/library/std/src//tests.rs

use core::num::FpCategory as Fp;
use decimalfp::decimal64::consts;
use decimalfp::prelude::*;
use decimalfp::*;

macro_rules! assert_approx_eq {
    ($a:expr, $b:expr) => {{
        let (a, b) = (&$a, &$b);
        assert!(
            (*a - *b).abs() < d64!(1.0e-6),
            "{} is not approximately equal to {}",
            *a,
            *b
        );
    }};
}

#[test]
fn test_min_nan_64() {
    assert_eq!(Decimal64::NAN.min(d64!(2.0)), d64!(2.0));
    assert_eq!(d64!(2.0).min(Decimal64::NAN), d64!(2.0));
}

#[test]
fn test_max_nan_64() {
    assert_eq!(Decimal64::NAN.max(d64!(2.0)), d64!(2.0));
    assert_eq!(d64!(2.0).max(Decimal64::NAN), d64!(2.0));
}

#[test]
fn test_nan_64() {
    let nan: Decimal64 = Decimal64::NAN;
    assert!(nan.is_nan());
    assert!(!nan.is_infinite());
    assert!(!nan.is_finite());
    assert!(!nan.is_normal());
    assert!(nan.is_sign_positive());
    assert!(!nan.is_sign_negative());
    assert_eq!(Fp::Nan, nan.classify());
}

#[test]
fn test_infinity_64() {
    let inf: Decimal64 = Decimal64::INFINITY;
    assert!(inf.is_infinite());
    assert!(!inf.is_finite());
    assert!(inf.is_sign_positive());
    assert!(!inf.is_sign_negative());
    assert!(!inf.is_nan());
    assert!(!inf.is_normal());
    assert_eq!(Fp::Infinite, inf.classify());
}

#[test]
fn test_neg_infinity_64() {
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert!(neg_inf.is_infinite());
    assert!(!neg_inf.is_finite());
    assert!(!neg_inf.is_sign_positive());
    assert!(neg_inf.is_sign_negative());
    assert!(!neg_inf.is_nan());
    assert!(!neg_inf.is_normal());
    assert_eq!(Fp::Infinite, neg_inf.classify());
}

#[test]
fn test_zero_64() {
    let zero: Decimal64 = d64!(0.0);
    assert_eq!(d64!(0.0), zero);
    assert!(!zero.is_infinite());
    assert!(zero.is_finite());
    assert!(zero.is_sign_positive());
    assert!(!zero.is_sign_negative());
    assert!(!zero.is_nan());
    assert!(!zero.is_normal());
    assert_eq!(Fp::Zero, zero.classify());
}

#[test]
fn test_neg_zero_64() {
    let neg_zero: Decimal64 = d64!(-0.0);
    assert_eq!(d64!(0.0), neg_zero);
    assert!(!neg_zero.is_infinite());
    assert!(neg_zero.is_finite());
    assert!(!neg_zero.is_sign_positive());
    assert!(neg_zero.is_sign_negative());
    assert!(!neg_zero.is_nan());
    assert!(!neg_zero.is_normal());
    assert_eq!(Fp::Zero, neg_zero.classify());
}

#[test]
fn test_one_64() {
    let one: Decimal64 = d64!(1.0);
    assert_eq!(d64!(1.0), one);
    assert!(!one.is_infinite());
    assert!(one.is_finite());
    assert!(one.is_sign_positive());
    assert!(!one.is_sign_negative());
    assert!(!one.is_nan());
    assert!(one.is_normal());
    assert_eq!(Fp::Normal, one.classify());
}

#[test]
fn test_is_nan_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert!(nan.is_nan());
    assert!(!d64!(0.0).is_nan());
    assert!(!d64!(5.3).is_nan());
    assert!(!d64!(-10.732).is_nan());
    assert!(!inf.is_nan());
    assert!(!neg_inf.is_nan());
}

#[test]
fn test_is_infinite_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert!(!nan.is_infinite());
    assert!(inf.is_infinite());
    assert!(neg_inf.is_infinite());
    assert!(!d64!(0.0).is_infinite());
    assert!(!d64!(42.8).is_infinite());
    assert!(!d64!(-109.2).is_infinite());
}

#[test]
fn test_is_finite_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert!(!nan.is_finite());
    assert!(!inf.is_finite());
    assert!(!neg_inf.is_finite());
    assert!(d64!(0.0).is_finite());
    assert!(d64!(42.8).is_finite());
    assert!(d64!(-109.2).is_finite());
}

#[test]
fn test_is_normal_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    let zero: Decimal64 = d64!(0.0);
    let neg_zero: Decimal64 = d64!(-0.0);
    assert!(!nan.is_normal());
    assert!(!inf.is_normal());
    assert!(!neg_inf.is_normal());
    assert!(!zero.is_normal());
    assert!(!neg_zero.is_normal());
    assert!(d64!(1).is_normal());
    assert!(d64!(1e-383).is_normal());
    assert!(!d64!(1e-384).is_normal());
}

#[test]
fn test_classify_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    let zero: Decimal64 = d64!(0.0);
    let neg_zero: Decimal64 = d64!(-0.0);
    assert_eq!(nan.classify(), Fp::Nan);
    assert_eq!(inf.classify(), Fp::Infinite);
    assert_eq!(neg_inf.classify(), Fp::Infinite);
    assert_eq!(zero.classify(), Fp::Zero);
    assert_eq!(neg_zero.classify(), Fp::Zero);
    assert_eq!(d64!(1e-383).classify(), Fp::Normal);
    assert_eq!(d64!(1e-384).classify(), Fp::Subnormal);
}

#[test]
fn test_floor_64() {
    assert_approx_eq!(d64!(1.0).floor(), d64!(1.0));
    assert_approx_eq!(d64!(1.3).floor(), d64!(1.0));
    assert_approx_eq!(d64!(1.5).floor(), d64!(1.0));
    assert_approx_eq!(d64!(1.7).floor(), d64!(1.0));
    assert_approx_eq!(d64!(0.0).floor(), d64!(0.0));
    assert_approx_eq!(d64!(-0.0).floor(), d64!(-0.0));
    assert_approx_eq!(d64!(-1.0).floor(), d64!(-1.0));
    assert_approx_eq!(d64!(-1.3).floor(), d64!(-2.0));
    assert_approx_eq!(d64!(-1.5).floor(), d64!(-2.0));
    assert_approx_eq!(d64!(-1.7).floor(), d64!(-2.0));
}

#[test]
fn test_ceil_64() {
    assert_approx_eq!(d64!(1.0).ceil(), d64!(1.0));
    assert_approx_eq!(d64!(1.3).ceil(), d64!(2.0));
    assert_approx_eq!(d64!(1.5).ceil(), d64!(2.0));
    assert_approx_eq!(d64!(1.7).ceil(), d64!(2.0));
    assert_approx_eq!(d64!(0.0).ceil(), d64!(0.0));
    assert_approx_eq!(d64!(-0.0).ceil(), d64!(-0.0));
    assert_approx_eq!(d64!(-1.0).ceil(), d64!(-1.0));
    assert_approx_eq!(d64!(-1.3).ceil(), d64!(-1.0));
    assert_approx_eq!(d64!(-1.5).ceil(), d64!(-1.0));
    assert_approx_eq!(d64!(-1.7).ceil(), d64!(-1.0));
}

#[test]
fn test_round_64() {
    assert_approx_eq!(d64!(1.0).round(), d64!(1.0));
    assert_approx_eq!(d64!(1.3).round(), d64!(1.0));
    assert_approx_eq!(d64!(1.5).round(), d64!(2.0));
    assert_approx_eq!(d64!(1.7).round(), d64!(2.0));
    assert_approx_eq!(d64!(0.0).round(), d64!(0.0));
    assert_approx_eq!(d64!(-0.0).round(), d64!(-0.0));
    assert_approx_eq!(d64!(-1.0).round(), d64!(-1.0));
    assert_approx_eq!(d64!(-1.3).round(), d64!(-1.0));
    assert_approx_eq!(d64!(-1.5).round(), d64!(-2.0));
    assert_approx_eq!(d64!(-1.7).round(), d64!(-2.0));
}

#[test]
fn test_trunc_64() {
    assert_approx_eq!(d64!(1.0).trunc(), d64!(1.0));
    assert_approx_eq!(d64!(1.3).trunc(), d64!(1.0));
    assert_approx_eq!(d64!(1.5).trunc(), d64!(1.0));
    assert_approx_eq!(d64!(1.7).trunc(), d64!(1.0));
    assert_approx_eq!(d64!(0.0).trunc(), d64!(0.0));
    assert_approx_eq!(d64!(-0.0).trunc(), d64!(-0.0));
    assert_approx_eq!(d64!(-1.0).trunc(), d64!(-1.0));
    assert_approx_eq!(d64!(-1.3).trunc(), d64!(-1.0));
    assert_approx_eq!(d64!(-1.5).trunc(), d64!(-1.0));
    assert_approx_eq!(d64!(-1.7).trunc(), d64!(-1.0));
}

#[test]
fn test_fract_64() {
    assert_approx_eq!(d64!(1.0).fract(), d64!(0.0));
    assert_approx_eq!(d64!(1.3).fract(), d64!(0.3));
    assert_approx_eq!(d64!(1.5).fract(), d64!(0.5));
    assert_approx_eq!(d64!(1.7).fract(), d64!(0.7));
    assert_approx_eq!(d64!(0.0).fract(), d64!(0.0));
    assert_approx_eq!(d64!(-0.0).fract(), d64!(-0.0));
    assert_approx_eq!(d64!(-1.0).fract(), d64!(-0.0));
    assert_approx_eq!(d64!(-1.3).fract(), d64!(-0.3));
    assert_approx_eq!(d64!(-1.5).fract(), d64!(-0.5));
    assert_approx_eq!(d64!(-1.7).fract(), d64!(-0.7));
}

#[test]
fn test_abs_64() {
    assert_eq!(Decimal64::INFINITY.abs(), Decimal64::INFINITY);
    assert_eq!(d64!(1).abs(), d64!(1));
    assert_eq!(d64!(0).abs(), d64!(0));
    assert_eq!(d64!(-0).abs(), d64!(0));
    assert_eq!(d64!(-1).abs(), d64!(1));
    assert_eq!(Decimal64::NEG_INFINITY.abs(), Decimal64::INFINITY);
    assert_eq!((d64!(1) / Decimal64::NEG_INFINITY).abs(), d64!(0));
    assert!(Decimal64::NAN.abs().is_nan());
}

#[test]
fn test_signum_64() {
    assert_eq!(Decimal64::INFINITY.signum(), d64!(1));
    assert_eq!(d64!(1).signum(), d64!(1));
    assert_eq!(d64!(0).signum(), d64!(1));
    assert_eq!(d64!(-0).signum(), d64!(-1));
    assert_eq!(d64!(-1).signum(), d64!(-1));
    assert_eq!(Decimal64::NEG_INFINITY.signum(), d64!(-1));
    assert_eq!((d64!(1) / Decimal64::NEG_INFINITY).signum(), d64!(-1));
    assert!(Decimal64::NAN.signum().is_nan());
}

#[test]
fn test_is_sign_positive_64() {
    assert!(Decimal64::INFINITY.is_sign_positive());
    assert!(d64!(1).is_sign_positive());
    assert!(d64!(0).is_sign_positive());
    assert!(!d64!(-0).is_sign_positive());
    assert!(!d64!(-1).is_sign_positive());
    assert!(!Decimal64::NEG_INFINITY.is_sign_positive());
    assert!(!(d64!(1) / Decimal64::NEG_INFINITY).is_sign_positive());
    assert!(Decimal64::NAN.is_sign_positive());
    assert!(!(-Decimal64::NAN).is_sign_positive());
}

#[test]
fn test_is_sign_negative_64() {
    assert!(!Decimal64::INFINITY.is_sign_negative());
    assert!(!d64!(1).is_sign_negative());
    assert!(!d64!(0).is_sign_negative());
    assert!(d64!(-0).is_sign_negative());
    assert!(d64!(-1).is_sign_negative());
    assert!(Decimal64::NEG_INFINITY.is_sign_negative());
    assert!((d64!(1) / Decimal64::NEG_INFINITY).is_sign_negative());
    assert!(!Decimal64::NAN.is_sign_negative());
    assert!((-Decimal64::NAN).is_sign_negative());
}

#[test]
fn test_mul_add_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert_approx_eq!(d64!(12.3).mul_add(d64!(4.5), d64!(6.7)), d64!(62.05));
    assert_approx_eq!(d64!(-12.3).mul_add(d64!(-4.5), d64!(-6.7)), d64!(48.65));
    assert_approx_eq!(d64!(0.0).mul_add(d64!(8.9), d64!(1.2)), d64!(1.2));
    assert_approx_eq!(d64!(3.4).mul_add(d64!(-0.0), d64!(5.6)), d64!(5.6));
    assert!(nan.mul_add(d64!(7.8), d64!(9.0)).is_nan());
    assert_eq!(inf.mul_add(d64!(7.8), d64!(9.0)), inf);
    assert_eq!(neg_inf.mul_add(d64!(7.8), d64!(9.0)), neg_inf);
    assert_eq!(d64!(8.9).mul_add(inf, d64!(3.2)), inf);
    assert_eq!(d64!(-3.2).mul_add(d64!(2.4), neg_inf), neg_inf);
}

#[test]
fn test_recip_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert_eq!(d64!(1.0).recip(), d64!(1.0));
    assert_eq!(d64!(2.0).recip(), d64!(0.5));
    assert_eq!(d64!(-0.4).recip(), d64!(-2.5));
    assert_eq!(d64!(0.0).recip(), inf);
    assert!(nan.recip().is_nan());
    assert_eq!(inf.recip(), d64!(0.0));
    assert_eq!(neg_inf.recip(), d64!(0.0));
}

#[test]
fn test_powi_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert_eq!(d64!(1.0).powi(1), d64!(1.0));
    assert_approx_eq!(d64!(-3.1).powi(2), d64!(9.61));
    assert_approx_eq!(d64!(5.9).powi(-2), d64!(0.028727));
    assert_eq!(d64!(8.3).powi(0), d64!(1.0));
    assert!(nan.powi(2).is_nan());
    assert_eq!(inf.powi(3), inf);
    assert_eq!(neg_inf.powi(2), inf);
}

#[test]
fn test_powf_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert_eq!(d64!(1.0).powf(d64!(1.0)), d64!(1.0));
    assert_approx_eq!(d64!(3.4).powf(d64!(4.5)), d64!(246.408183));
    assert_approx_eq!(d64!(2.7).powf(d64!(-3.2)), d64!(0.041652));
    assert_approx_eq!(d64!(-3.1).powf(d64!(2.0)), d64!(9.61));
    assert_approx_eq!(d64!(5.9).powf(d64!(-2.0)), d64!(0.028727));
    assert_eq!(d64!(8.3).powf(d64!(0.0)), d64!(1.0));
    assert!(nan.powf(d64!(2.0)).is_nan());
    assert_eq!(inf.powf(d64!(2.0)), inf);
    assert_eq!(neg_inf.powf(d64!(3.0)), neg_inf);
}

#[test]
fn test_sqrt_domain_64() {
    assert!(Decimal64::NAN.sqrt().is_nan());
    assert!(Decimal64::NEG_INFINITY.sqrt().is_nan());
    assert!(d64!(-1.0).sqrt().is_nan());
    assert_eq!(d64!(-0.0).sqrt(), d64!(-0.0));
    assert_eq!(d64!(0.0).sqrt(), d64!(0.0));
    assert_eq!(d64!(1.0).sqrt(), d64!(1.0));
    assert_eq!(Decimal64::INFINITY.sqrt(), Decimal64::INFINITY);
}

#[test]
fn test_exp_64() {
    assert_eq!(d64!(1.0), d64!(0.0).exp());
    assert_approx_eq!(d64!(2.718282), d64!(1.0).exp());
    assert_approx_eq!(d64!(148.413159), d64!(5.0).exp());

    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    let nan: Decimal64 = Decimal64::NAN;
    assert_eq!(inf, inf.exp());
    assert_eq!(d64!(0.0), neg_inf.exp());
    assert!(nan.exp().is_nan());
}

#[test]
fn test_exp2_64() {
    assert_eq!(d64!(32.0), d64!(5.0).exp2());
    assert_eq!(d64!(1.0), d64!(0.0).exp2());

    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    let nan: Decimal64 = Decimal64::NAN;
    assert_eq!(inf, inf.exp2());
    assert_eq!(d64!(0.0), neg_inf.exp2());
    assert!(nan.exp2().is_nan());
}

#[test]
fn test_ln_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert_approx_eq!(d64!(1.0).exp().ln(), d64!(1.0));
    assert!(nan.ln().is_nan());
    assert_eq!(inf.ln(), inf);
    assert!(neg_inf.ln().is_nan());
    assert!(d64!(-2.3).ln().is_nan());
    assert_eq!(d64!(-0.0).ln(), neg_inf);
    assert_eq!(d64!(0.0).ln(), neg_inf);
    assert_approx_eq!(d64!(4.0).ln(), d64!(1.386294));
}

#[test]
fn test_log_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert_eq!(d64!(10.0).log(d64!(10.0)), d64!(1.0));
    assert_approx_eq!(d64!(2.3).log(d64!(3.5)), d64!(0.664858));
    assert_eq!(d64!(1.0).exp().log(d64!(1.0).exp()), d64!(1.0));
    assert!(d64!(1.0).log(d64!(1.0)).is_nan());
    assert!(d64!(1.0).log(d64!(-13.9)).is_nan());
    assert!(nan.log(d64!(2.3)).is_nan());
    assert_eq!(inf.log(d64!(10.0)), inf);
    assert!(neg_inf.log(d64!(8.8)).is_nan());
    assert!(d64!(-2.3).log(d64!(0.1)).is_nan());
    assert_eq!(d64!(-0.0).log(d64!(2.0)), neg_inf);
    assert_eq!(d64!(0.0).log(d64!(7.0)), neg_inf);
}

#[test]
fn test_log2_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert_approx_eq!(d64!(10.0).log2(), d64!(3.321928));
    assert_approx_eq!(d64!(2.3).log2(), d64!(1.201634));
    assert_approx_eq!(d64!(1.0).exp().log2(), d64!(1.442695));
    assert!(nan.log2().is_nan());
    assert_eq!(inf.log2(), inf);
    assert!(neg_inf.log2().is_nan());
    assert!(d64!(-2.3).log2().is_nan());
    assert_eq!(d64!(-0.0).log2(), neg_inf);
    assert_eq!(d64!(0.0).log2(), neg_inf);
}

#[test]
fn test_log10_64() {
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert_eq!(d64!(10.0).log10(), d64!(1.0));
    assert_approx_eq!(d64!(2.3).log10(), d64!(0.361728));
    assert_approx_eq!(d64!(1.0).exp().log10(), d64!(0.434294));
    assert_eq!(d64!(1.0).log10(), d64!(0.0));
    assert!(nan.log10().is_nan());
    assert_eq!(inf.log10(), inf);
    assert!(neg_inf.log10().is_nan());
    assert!(d64!(-2.3).log10().is_nan());
    assert_eq!(d64!(-0.0).log10(), neg_inf);
    assert_eq!(d64!(0.0).log10(), neg_inf);
}

#[test]
fn test_to_degrees_64() {
    let pi: Decimal64 = consts::PI;
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert_eq!(d64!(0.0).to_degrees(), d64!(0.0));
    assert_approx_eq!(d64!(-5.8).to_degrees(), d64!(-332.315521));
    assert_eq!(pi.to_degrees(), d64!(180.0));
    assert!(nan.to_degrees().is_nan());
    assert_eq!(inf.to_degrees(), inf);
    assert_eq!(neg_inf.to_degrees(), neg_inf);
}

#[test]
fn test_to_radians_64() {
    let pi: Decimal64 = consts::PI;
    let nan: Decimal64 = Decimal64::NAN;
    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    assert_eq!(d64!(0.0).to_radians(), d64!(0.0));
    assert_approx_eq!(d64!(154.6).to_radians(), d64!(2.698279));
    assert_approx_eq!(d64!(-332.31).to_radians(), d64!(-5.799903));
    assert_eq!(d64!(180.0).to_radians(), pi);
    assert!(nan.to_radians().is_nan());
    assert_eq!(inf.to_radians(), inf);
    assert_eq!(neg_inf.to_radians(), neg_inf);
}

#[test]
fn test_asinh_64() {
    assert_eq!(d64!(0.0).asinh(), d64!(0.0));
    assert_eq!(d64!(-0.0).asinh(), d64!(-0.0));

    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    let nan: Decimal64 = Decimal64::NAN;
    assert_eq!(inf.asinh(), inf);
    assert_eq!(neg_inf.asinh(), neg_inf);
    assert!(nan.asinh().is_nan());
    assert!(d64!(-0.0).asinh().is_sign_negative());
    // issue 63271
    assert_approx_eq!(d64!(2.0).asinh(), d64!(1.443635475178810342493276740273105));
    assert_approx_eq!(
        d64!(-2.0).asinh(),
        d64!(-1.443635475178810342493276740273105)
    );
    // regression test for the catastrophic cancellation fixed in 72486
    assert_approx_eq!(
        d64!(-67452098.07139316).asinh(),
        d64!(-18.72007542627454439398548429400083)
    );
}

#[test]
fn test_acosh_64() {
    assert_eq!(d64!(1.0).acosh(), d64!(0.0));
    assert!(d64!(0.999).acosh().is_nan());

    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    let nan: Decimal64 = Decimal64::NAN;
    assert_eq!(inf.acosh(), inf);
    assert!(neg_inf.acosh().is_nan());
    assert!(nan.acosh().is_nan());
    assert_approx_eq!(
        d64!(2.0).acosh(),
        d64!(1.31695789692481670862504634730796844)
    );
    assert_approx_eq!(
        d64!(3.0).acosh(),
        d64!(1.76274717403908605046521864995958461)
    );
}

#[test]
fn test_atanh_64() {
    assert_eq!(d64!(0.0).atanh(), d64!(0.0));
    assert_eq!(d64!(-0.0).atanh(), d64!(-0.0));

    let inf: Decimal64 = Decimal64::INFINITY;
    let neg_inf: Decimal64 = Decimal64::NEG_INFINITY;
    let nan: Decimal64 = Decimal64::NAN;
    assert_eq!(d64!(1.0).atanh(), inf);
    assert_eq!(d64!(-1.0).atanh(), neg_inf);
    assert!(d64!(2).atanh().atanh().is_nan());
    assert!(d64!(-2).atanh().atanh().is_nan());
    assert!(inf.atanh().is_nan());
    assert!(neg_inf.atanh().is_nan());
    assert!(nan.atanh().is_nan());
    assert_approx_eq!(
        d64!(0.5).atanh(),
        d64!(0.54930614433405484569762261846126285)
    );
    assert_approx_eq!(
        d64!(-0.5).atanh(),
        d64!(-0.54930614433405484569762261846126285)
    );
}

#[test]
fn test_real_consts_64() {
    use decimal64::consts;
    let pi: Decimal64 = consts::PI;
    let frac_pi_2: Decimal64 = consts::FRAC_PI_2;
    let frac_pi_3: Decimal64 = consts::FRAC_PI_3;
    let frac_pi_4: Decimal64 = consts::FRAC_PI_4;
    let frac_pi_6: Decimal64 = consts::FRAC_PI_6;
    let frac_pi_8: Decimal64 = consts::FRAC_PI_8;
    let frac_1_pi: Decimal64 = consts::FRAC_1_PI;
    let frac_2_pi: Decimal64 = consts::FRAC_2_PI;
    let frac_2_sqrtpi: Decimal64 = consts::FRAC_2_SQRT_PI;
    let sqrt2: Decimal64 = consts::SQRT_2;
    let frac_1_sqrt2: Decimal64 = consts::FRAC_1_SQRT_2;
    let e: Decimal64 = consts::E;
    let log2_e: Decimal64 = consts::LOG2_E;
    let log10_e: Decimal64 = consts::LOG10_E;
    let ln_2: Decimal64 = consts::LN_2;
    let ln_10: Decimal64 = consts::LN_10;

    assert_approx_eq!(frac_pi_2, pi / d64!(2));
    assert_approx_eq!(frac_pi_3, pi / d64!(3));
    assert_approx_eq!(frac_pi_4, pi / d64!(4));
    assert_approx_eq!(frac_pi_6, pi / d64!(6));
    assert_approx_eq!(frac_pi_8, pi / d64!(8));
    assert_approx_eq!(frac_1_pi, d64!(1) / pi);
    assert_approx_eq!(frac_2_pi, d64!(2) / pi);
    assert_approx_eq!(frac_2_sqrtpi, d64!(2) / pi.sqrt());
    assert_approx_eq!(sqrt2, d64!(2).sqrt());
    assert_approx_eq!(frac_1_sqrt2, d64!(1) / d64!(2).sqrt());
    assert_approx_eq!(log2_e, e.log2());
    assert_approx_eq!(log10_e, e.log10());
    assert_approx_eq!(ln_2, d64!(2).ln());
    assert_approx_eq!(ln_10, d64!(10).ln());
}

#[test]
fn test_float_bits_conv_64() {
    assert_eq!(d64!(1).to_bits(), 0x31c0000000000001);
    assert_eq!(d64!(12.5).to_bits(), 0x31a000000000007d);
    assert_eq!(d64!(1337).to_bits(), 0x31c0000000000539);
    assert_eq!(d64!(-14.25).to_bits(), 0xb180000000000591);
    assert_eq!(Decimal64::from_bits(0x31c0000000000001), d64!(1.0));
    assert_eq!(Decimal64::from_bits(0x31a000000000007d), d64!(12.5));
    assert_eq!(Decimal64::from_bits(0x31c0000000000539), d64!(1337.0));
    assert_eq!(Decimal64::from_bits(0xb180000000000591), d64!(-14.25));

    // Check that NaNs roundtrip their bits regardless of signaling-ness
    // 0xA is 0b1010; 0x5 is 0b0101 -- so these two together clobbers all the mantissa bits
    let masked_nan1 = Decimal64::NAN.to_bits() ^ 0x00AA_AAAA_AAAA_AAAA;
    let masked_nan2 = Decimal64::NAN.to_bits() ^ 0x0055_5555_5555_5555;
    assert!(Decimal64::from_bits(masked_nan1).is_nan());
    assert!(Decimal64::from_bits(masked_nan2).is_nan());

    assert_eq!(Decimal64::from_bits(masked_nan1).to_bits(), masked_nan1);
    assert_eq!(Decimal64::from_bits(masked_nan2).to_bits(), masked_nan2);
}

#[test]
#[should_panic]
fn test_clamp_min_greater_than_max_64() {
    let _ = d64!(1.0).clamp(d64!(3.0), d64!(1.0));
}

#[test]
#[should_panic]
fn test_clamp_min_is_nan_64() {
    let _ = d64!(1.0).clamp(Decimal64::NAN, d64!(1.0));
}

#[test]
#[should_panic]
fn test_clamp_max_is_nan_64() {
    let _ = d64!(1.0).clamp(d64!(3.0), Decimal64::NAN);
}

#[test]
fn test_total_cmp_64() {
    use core::cmp::Ordering;
    fn min_subnorm() -> Decimal64 {
        Decimal64::MIN_POSITIVE
            / Decimal64::powf(
                d64!(10.0),
                Decimal64::from_int(Decimal64::MANTISSA_DIGITS) - d64!(1.0),
            )
    }
    fn max_subnorm() -> Decimal64 {
        Decimal64::MIN_POSITIVE - min_subnorm()
    }
    fn q_nan() -> Decimal64 {
        Decimal64::NAN
    }
    fn s_nan() -> Decimal64 {
        Decimal64::SNAN
    }

    assert_eq!(Ordering::Equal, (-q_nan()).total_cmp(&-q_nan()));
    assert_eq!(Ordering::Equal, (-s_nan()).total_cmp(&-s_nan()));
    assert_eq!(
        Ordering::Equal,
        (-Decimal64::INFINITY).total_cmp(&-Decimal64::INFINITY)
    );
    assert_eq!(
        Ordering::Equal,
        (-Decimal64::MAX).total_cmp(&-Decimal64::MAX)
    );
    assert_eq!(Ordering::Equal, d64!(-2.5).total_cmp(&d64!(-2.5)));
    assert_eq!(Ordering::Equal, d64!(-1.0).total_cmp(&d64!(-1.0)));
    assert_eq!(Ordering::Equal, d64!(-1.5).total_cmp(&d64!(-1.5)));
    assert_eq!(Ordering::Equal, d64!(-0.5).total_cmp(&d64!(-0.5)));
    assert_eq!(
        Ordering::Equal,
        (-Decimal64::MIN_POSITIVE).total_cmp(&-Decimal64::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Equal, (-max_subnorm()).total_cmp(&-max_subnorm()));
    assert_eq!(Ordering::Equal, (-min_subnorm()).total_cmp(&-min_subnorm()));
    assert_eq!(Ordering::Equal, d64!(-0.0).total_cmp(&d64!(-0.0)));
    assert_eq!(Ordering::Equal, d64!(0.0).total_cmp(&d64!(0.0)));
    assert_eq!(Ordering::Equal, min_subnorm().total_cmp(&min_subnorm()));
    assert_eq!(Ordering::Equal, max_subnorm().total_cmp(&max_subnorm()));
    assert_eq!(
        Ordering::Equal,
        Decimal64::MIN_POSITIVE.total_cmp(&Decimal64::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Equal, d64!(0.5).total_cmp(&d64!(0.5)));
    assert_eq!(Ordering::Equal, d64!(1.0).total_cmp(&d64!(1.0)));
    assert_eq!(Ordering::Equal, d64!(1.5).total_cmp(&d64!(1.5)));
    assert_eq!(Ordering::Equal, d64!(2.5).total_cmp(&d64!(2.5)));
    assert_eq!(Ordering::Equal, Decimal64::MAX.total_cmp(&Decimal64::MAX));
    assert_eq!(
        Ordering::Equal,
        Decimal64::INFINITY.total_cmp(&Decimal64::INFINITY)
    );
    assert_eq!(Ordering::Equal, s_nan().total_cmp(&s_nan()));
    assert_eq!(Ordering::Equal, q_nan().total_cmp(&q_nan()));

    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-s_nan()));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&-Decimal64::INFINITY));
    assert_eq!(
        Ordering::Less,
        (-Decimal64::INFINITY).total_cmp(&-Decimal64::MAX)
    );
    assert_eq!(Ordering::Less, (-Decimal64::MAX).total_cmp(&d64!(-2.5)));
    assert_eq!(Ordering::Less, d64!(-2.5).total_cmp(&d64!(-1.5)));
    assert_eq!(Ordering::Less, d64!(-1.5).total_cmp(&d64!(-1.0)));
    assert_eq!(Ordering::Less, d64!(-1.0).total_cmp(&d64!(-0.5)));
    assert_eq!(
        Ordering::Less,
        d64!(-0.5).total_cmp(&-Decimal64::MIN_POSITIVE)
    );
    assert_eq!(
        Ordering::Less,
        (-Decimal64::MIN_POSITIVE).total_cmp(&-max_subnorm())
    );
    assert_eq!(Ordering::Less, (-max_subnorm()).total_cmp(&-min_subnorm()));
    assert_eq!(Ordering::Less, (-min_subnorm()).total_cmp(&d64!(-0.0)));
    assert_eq!(Ordering::Less, d64!(-0.0).total_cmp(&d64!(0.0)));
    assert_eq!(Ordering::Less, d64!(0.0).total_cmp(&min_subnorm()));
    assert_eq!(Ordering::Less, min_subnorm().total_cmp(&max_subnorm()));
    assert_eq!(
        Ordering::Less,
        max_subnorm().total_cmp(&Decimal64::MIN_POSITIVE)
    );
    assert_eq!(
        Ordering::Less,
        Decimal64::MIN_POSITIVE.total_cmp(&d64!(0.5))
    );
    assert_eq!(Ordering::Less, d64!(0.5).total_cmp(&d64!(1.0)));
    assert_eq!(Ordering::Less, d64!(1.0).total_cmp(&d64!(1.5)));
    assert_eq!(Ordering::Less, d64!(1.5).total_cmp(&d64!(2.5)));
    assert_eq!(Ordering::Less, d64!(2.5).total_cmp(&Decimal64::MAX));
    assert_eq!(
        Ordering::Less,
        Decimal64::MAX.total_cmp(&Decimal64::INFINITY)
    );
    assert_eq!(Ordering::Less, Decimal64::INFINITY.total_cmp(&s_nan()));
    assert_eq!(Ordering::Less, s_nan().total_cmp(&q_nan()));

    assert_eq!(Ordering::Greater, (-s_nan()).total_cmp(&-q_nan()));
    assert_eq!(
        Ordering::Greater,
        (-Decimal64::INFINITY).total_cmp(&-s_nan())
    );
    assert_eq!(
        Ordering::Greater,
        (-Decimal64::MAX).total_cmp(&-Decimal64::INFINITY)
    );
    assert_eq!(Ordering::Greater, d64!(-2.5).total_cmp(&-Decimal64::MAX));
    assert_eq!(Ordering::Greater, d64!(-1.5).total_cmp(&d64!(-2.5)));
    assert_eq!(Ordering::Greater, d64!(-1.0).total_cmp(&d64!(-1.5)));
    assert_eq!(Ordering::Greater, d64!(-0.5).total_cmp(&d64!(-1.0)));
    assert_eq!(
        Ordering::Greater,
        (-Decimal64::MIN_POSITIVE).total_cmp(&d64!(-0.5))
    );
    assert_eq!(
        Ordering::Greater,
        (-max_subnorm()).total_cmp(&-Decimal64::MIN_POSITIVE)
    );
    assert_eq!(
        Ordering::Greater,
        (-min_subnorm()).total_cmp(&-max_subnorm())
    );
    assert_eq!(Ordering::Greater, d64!(-0.0).total_cmp(&-min_subnorm()));
    assert_eq!(Ordering::Greater, d64!(0.0).total_cmp(&d64!(-0.0)));
    assert_eq!(Ordering::Greater, min_subnorm().total_cmp(&d64!(0.0)));
    assert_eq!(Ordering::Greater, max_subnorm().total_cmp(&min_subnorm()));
    assert_eq!(
        Ordering::Greater,
        Decimal64::MIN_POSITIVE.total_cmp(&max_subnorm())
    );
    assert_eq!(
        Ordering::Greater,
        d64!(0.5).total_cmp(&Decimal64::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Greater, d64!(1.0).total_cmp(&d64!(0.5)));
    assert_eq!(Ordering::Greater, d64!(1.5).total_cmp(&d64!(1.0)));
    assert_eq!(Ordering::Greater, d64!(2.5).total_cmp(&d64!(1.5)));
    assert_eq!(Ordering::Greater, Decimal64::MAX.total_cmp(&d64!(2.5)));
    assert_eq!(
        Ordering::Greater,
        Decimal64::INFINITY.total_cmp(&Decimal64::MAX)
    );
    assert_eq!(Ordering::Greater, s_nan().total_cmp(&Decimal64::INFINITY));
    assert_eq!(Ordering::Greater, q_nan().total_cmp(&s_nan()));

    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-s_nan()));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-Decimal64::INFINITY));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-Decimal64::MAX));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d64!(-2.5)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d64!(-1.5)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d64!(-1.0)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d64!(-0.5)));
    assert_eq!(
        Ordering::Less,
        (-q_nan()).total_cmp(&-Decimal64::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-max_subnorm()));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&-min_subnorm()));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d64!(-0.0)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d64!(0.0)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&min_subnorm()));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&max_subnorm()));
    assert_eq!(
        Ordering::Less,
        (-q_nan()).total_cmp(&Decimal64::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d64!(0.5)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d64!(1.0)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d64!(1.5)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&d64!(2.5)));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&Decimal64::MAX));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&Decimal64::INFINITY));
    assert_eq!(Ordering::Less, (-q_nan()).total_cmp(&s_nan()));

    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&-Decimal64::INFINITY));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&-Decimal64::MAX));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d64!(-2.5)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d64!(-1.5)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d64!(-1.0)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d64!(-0.5)));
    assert_eq!(
        Ordering::Less,
        (-s_nan()).total_cmp(&-Decimal64::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&-max_subnorm()));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&-min_subnorm()));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d64!(-0.0)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d64!(0.0)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&min_subnorm()));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&max_subnorm()));
    assert_eq!(
        Ordering::Less,
        (-s_nan()).total_cmp(&Decimal64::MIN_POSITIVE)
    );
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d64!(0.5)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d64!(1.0)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d64!(1.5)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&d64!(2.5)));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&Decimal64::MAX));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&Decimal64::INFINITY));
    assert_eq!(Ordering::Less, (-s_nan()).total_cmp(&s_nan()));
}
