use std::str::FromStr;

use decimalfp::{context::Context, *};

macro_rules! print_val {
    ($val:expr) => {{
        let val = $val;
        println!(
            "{}: 0x{:X} decode: {:?}",
            val,
            val.to_bits(),
            val.integer_decode()
        );
    }};
}

macro_rules! print_dec {
    ($lit:expr) => {
        print_val!(d32!($lit));
        print_val!(d64!($lit));
        print_val!(d128!($lit));
    };
}

#[test]
fn print_32() {
    println!("{}", d32!(1.2));
}

#[test]
fn print_64() {
    println!("{}", d64!(1.2));
}

#[test]
fn print_128() {
    println!("{}", d128!(1.2));
}

#[test]
fn print() {
    print_dec!(0);
    print_dec!(-0);
    print_dec!(0.5);
    print_dec!(1);
    print_dec!(-1);
    print_dec!(2);
    print_dec!(3);
    print_dec!(4);
    print_dec!(5);
    print_dec!(6);
    print_dec!(7);
    print_dec!(8);
    print_dec!(9);
    print_dec!(10);
    print_dec!(1000);
    print_dec!(1024);

    println!("PI");
    print_dec!(3.1415926535897932384626433832795028841971693993751058209749445923);

    println!("TAU");
    print_dec!(6.2831853071795864769252867665590057683943387987502116419498891846);

    println!("FRAC_PI_2");
    print_dec!(1.5707963267948966192313216916397514420985846996875529104874722961);

    println!("FRAC_PI_3");
    print_dec!(1.0471975511965977461542144610931676280657231331250352736583148641);

    println!("FRAC_PI_4");
    print_dec!(0.7853981633974483096156608458198757210492923498437764552437361480);

    println!("FRAC_PI_6");
    print_dec!(0.5235987755982988730771072305465838140328615665625176368291574320);

    println!("FRAC_PI_8");
    print_dec!(0.3926990816987241548078304229099378605246461749218882276218680740);

    println!("FRAC_PI_180");
    print_dec!(0.0174532925199432957692369076848861271344287188854172545609719144);

    println!("FRAC_1_PI");
    print_dec!(0.3183098861837906715377675267450287240689192914809128974953346881);

    println!("FRAC_2_PI");
    print_dec!(0.6366197723675813430755350534900574481378385829618257949906693762);

    println!("FRAC_180_PI");
    print_dec!(57.295779513082320876798154814105170332405472466564321549160243861);

    println!("FRAC_2_SQRT_PI");
    print_dec!(1.1283791670955125738961589031215451716881012586579977136881714434);

    println!("SQRT_2");
    print_dec!(1.4142135623730950488016887242096980785696718753769480731766797379);

    println!("FRAC_1_SQRT_2");
    print_dec!(0.7071067811865475244008443621048490392848359376884740365883398689);

    println!("E");
    print_dec!(2.7182818284590452353602874713526624977572470936999595749669676277);

    println!("LOG2_10");
    print_dec!(3.3219280948873623478703194294893901758648313930245806120547563958);

    println!("LOG2_E");
    print_dec!(1.4426950408889634073599246810018921374266459541529859341354494069);

    println!("LOG10_2");
    print_dec!(0.3010299956639811952137388947244930267681898814621085413104274611);

    println!("LOG10_E");
    print_dec!(0.4342944819032518276511289189166050822943970058036665661144537831);

    println!("LN_2");
    print_dec!(0.6931471805599453094172321214581765680755001343602552541206800094);

    println!("LN_10");
    print_dec!(2.3025850929940456840179914546843642076011014886287729760333279009);

    println!("EPSILON");
    print_val!(d32!(1E-6));
    print_val!(d64!(1E-15));
    print_val!(d128!(1E-33));

    println!("MIN");
    print_val!(d32!(-9.999999E96));
    print_val!(d64!(-9.999999999999999E384));
    print_val!(d128!(-9.999999999999999999999999999999999E6144));

    println!("MIN_POSITIVE");
    print_val!(d32!(1E-95));
    print_val!(d64!(1E-383));
    print_val!(d128!(1E-6143));

    println!("SUBNORMAL_MIN_POSITIVE");
    print_val!(d32!(0.000001E-95));
    print_val!(d64!(0.000000000000001E-383));
    print_val!(d128!(0.000000000000000000000000000000001E-6143));

    println!("MAX");
    print_val!(d32!(9.999999E96));
    print_val!(d64!(9.999999999999999E384));
    print_val!(d128!(9.999999999999999999999999999999999E6144));

    println!("rng exps");
    print_val!(d32!(1E-7));
    print_val!(d64!(1E-16));
    print_val!(d128!(1E-34));
}

#[test]
fn conversions() {
    let d = dbg!(d32!(-32768.1e1));
    let mut ctx = Context::default();
    let _: u16 = dbg!(ctx.to_int_exact_trunc(d));
    dbg!(ctx);
}

#[test]
fn conversions2() {
    let d = dbg!(d64!(-0.0));
    let mut ctx = Context::default();
    let _: u16 = dbg!(ctx.to_int_exact_floor(d));
    dbg!(ctx);
}

#[test]
fn to_integral() {
    let d = dbg!(d64!(200000E-5));
    let mut ctx = Context::default();
    dbg!(ctx.round(d));
    dbg!(ctx);
}

#[test]
fn to_big() {
    dbg!(d128!(2222222222220).to_int::<u8>());
}

#[test]
#[cfg(feature = "primitive-types")]
fn from_big() {
    dbg!(Decimal32::from_int(primitive_types::U256::MAX));
}

#[cfg(feature = "ndarray")]
#[test]
fn ndarray() {
    use ndarray::array;

    dbg!(array![[d32!(1.0), d32!(2.0)]] * array![[d32!(1.0)], [d32!(2.0)]]);
}

#[cfg(feature = "rust_decimal")]
#[test]
fn rust_decimal() {
    let d: Decimal128 = dbg!(d128!(353335.313452467654999999999999999));
    let _ = dbg!(rust_decimal::Decimal::try_from(d));
}

#[test]
fn context() {
    Context::default().trunc::<Decimal64>(FromStr::from_str("34.5").unwrap());
}

#[cfg(feature = "allow_overflowing_literals")]
#[test]
fn overflowing_literal() {
    let _ = dbg!(d32!(-1e20000));
    //let _ = dbg!(d32!(nan));
}
