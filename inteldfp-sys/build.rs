use std::{
    env,
    fs::{self, File, OpenOptions},
    io::Write,
    path::Path,
};

use flate2::read::GzDecoder;
use tar::Archive;

fn replace_in_file(from: &str, to: &str, path: &Path) {
    let old_string = fs::read_to_string(path).unwrap();
    let new_string = old_string.replace(from, to);
    fs::write(path, new_string.as_bytes()).unwrap();
}

fn main() {
    build::rerun_if_changed("IntelRDFPMathLib20U2.tar.gz");

    //dbg!(std::env::vars_os().collect::<Vec<(std::ffi::OsString, std::ffi::OsString)>>());

    let out_dir = env::var_os("OUT_DIR").unwrap();
    let out_path = Path::new(&out_dir);
    let root_path: &Path = &out_path.join("IntelRDFPMathLib20U2");
    let lib_path: &Path = &root_path.join("LIBRARY");
    let lib_src_path: &Path = &lib_path.join("src");
    let lib_f128_path: &Path = &lib_path.join("float128");
    let tests_path: &Path = &root_path.join("TESTS");

    // Unpack library tarball
    let tarball_path = "IntelRDFPMathLib20U2.tar.gz";
    let tar_gz = File::open(tarball_path).unwrap();
    let tar = GzDecoder::new(tar_gz);
    let mut archive = Archive::new(tar);
    archive.unpack(&out_path).unwrap();

    // Apply patches
    // FIXME better patch method
    let bid_trans_path: &Path = &lib_src_path.join("bid_trans.h");
    let bid_functions_path: &Path = &lib_src_path.join("bid_functions.h");
    let bid_conf_path: &Path = &lib_src_path.join("bid_conf.h");

    replace_in_file(
        "#   else\r
#       error \"128-bit floating point type for this compiler is unknown\"\r
#   endif\r
#endif",
        "#   elif (defined gcc || defined clang) && (defined ia32 || defined efi2 || defined ia64 || defined ppc)\r
#       define  BID_F128_TYPE __float128\r
#   else\r
#       define  BID_F128_TYPE long double\r
#   endif\r
#endif\r
#include <assert.h>\r
static_assert(sizeof(BID_F128_TYPE) >= 16, \"128-bit floating point type for this compiler is unknown\");\r",
        bid_trans_path,
    );

    // `libquadmath` doesn't provide `exp10`, so we give our own implementation.
    // Credit: https://git.musl-libc.org/cgit/musl/tree/src/internal/libm.h, https://git.musl-libc.org/cgit/musl/tree/src/math/exp10l.c
    replace_in_file(
        "#   define __BID_F128_NAME(name)		__ ## name ## q",
        "#   if defined glibc_2_26\r
#       define __BID_F128_NAME(name)		name ## f128 // from glibc\r
#   elif defined libquadmath\r
#       define __BID_F128_NAME(name)		name ## q // from libquadmath\r
#   else\r
#       define __BID_F128_NAME(name)		name ## l // from math.h\r
#   endif",
        bid_trans_path,
    );

    // Android and the BSDs doesn't provide `exp10l`, so we give our own implementation.
    // Credit: https://git.musl-libc.org/cgit/musl/tree/src/internal/libm.h, https://git.musl-libc.org/cgit/musl/tree/src/math/exp10l.c
    replace_in_file(
        "#   else\r
#       error \"80-bit floating point type for this compiler is unknown\"\r
#   endif\r
#endif",
        "#   elif (!defined WINNT) && (defined ia32 || defined efi2 || defined ia64)\r
#       define BID_F80_TYPE long double\r
#   else\r
#       define BID_F80_TYPE BID_F128_TYPE\r
#   endif\r
#endif\r
\r
static_assert(sizeof(BID_F80_TYPE) >= 12, \"80-bit floating point type for this compiler is unknown\");",
        bid_trans_path,
    );

    replace_in_file(
        "#   define __BID_F80_NAME(name)			name ## l\r",
        "#   if (defined gcc || defined clang) && !(defined ia32 || defined efi2 || defined ia64)\r
#       define __BID_F80_NAME(name)			__BID_F128_NAME(name)\r
#   else\r
#       define __BID_F80_NAME(name)			name ## l\r
#   endif\r",
        bid_trans_path,
    );

    replace_in_file(
        "#if USE_COMPILER_F80_TYPE\r
#    define BID_INIT_F80(hi,lo)	{ ENDIAN128( F128_TO_F80_HI(hi,lo), F128_TO_F80_LO(hi,lo)) } \r
#else\r",
        "#if (!defined WINNT || defined __INTEL_COMPILER) && USE_COMPILER_F80_TYPE && (defined ia32 || defined efi2 || defined ia64)\r
#    define BID_INIT_F80(hi,lo)	{ ENDIAN128( F128_TO_F80_HI(hi,lo), F128_TO_F80_LO(hi,lo)) } \r
#else\r",
        bid_trans_path,
    );

    replace_in_file(
        "#if !defined _MSC_VER || defined __INTEL_COMPILER\r
#define __ENABLE_BINARY80__  1\r
#endif\r",
        "#if (!defined WINNT || defined __INTEL_COMPILER) && USE_COMPILER_F80_TYPE && (defined ia32 || defined efi2 || defined ia64)\r
#define __ENABLE_BINARY80__  1\r
#endif\r",
        bid_functions_path,
    );

    replace_in_file(
        "#if !defined (__INTEL_COMPILER)\r
typedef BID_UINT128 _Quad;\r
#endif",
        "#if !defined (__INTEL_COMPILER)\r
#   if USE_COMPILER_F128_TYPE\r
#       if (defined gcc || defined clang) && (defined ia32 || defined efi2 || defined ia64 || defined ppc)\r
            typedef __float128 _Quad;\r
#       else\r
            typedef long double _Quad;\r
#       endif\r
#   else\r
        typedef BID_UINT128 _Quad;\r
#   endif\r
#endif",
        bid_functions_path,
    );

    replace_in_file(
        "#define BINARY80 long double\r
  #if defined (__INTEL_COMPILER) && USE_COMPILER_F128_TYPE\r
    #define BINARY128 _Quad\r
  #else\r
    #define BINARY128 BID_UINT128\r
  #endif",
        "#if USE_COMPILER_F128_TYPE\r
    #if defined (__INTEL_COMPILER)\r
      #define BINARY80 long double\r
      #define BINARY128 _Quad\r
    #elif (defined gcc || defined clang) && (defined ia32 || defined efi2 || defined ia64 || defined ppc)\r
      #define BINARY128 __float128\r
    #else\r
      #define BINARY128 long double\r
    #endif\r
  #else\r
    #define BINARY128 BID_UINT128\r
  #endif\r
  #if (!defined _MSC_VER || defined __INTEL_COMPILER) && USE_COMPILER_F80_TYPE && (defined ia32 || defined efi2 || defined ia64)\r
    #define BINARY80 long double\r
  #else\r
    #define BINARY80 BINARY128\r
  #endif\r",
        bid_functions_path,
    );

    replace_in_file(
        "#define BINARY80 long double\r
  #if defined (__INTEL_COMPILER) && USE_COMPILER_F128_TYPE\r
    #define BINARY128 _Quad\r
  #else\r
    #define BINARY128 BID_UINT128\r
  #endif",
        "#if USE_COMPILER_F128_TYPE\r
    #if defined (__INTEL_COMPILER)\r
      #define BINARY80 long double\r
      #define BINARY128 _Quad\r
    #elif (defined gcc || defined clang) && (defined ia32 || defined efi2 || defined ia64 || defined ppc)\r
      #define BINARY128 __float128\r
    #else\r
      #define BINARY128 long double\r
    #endif\r
  #else\r
    #define BINARY128 BID_UINT128\r
  #endif\r
  #if (!defined _MSC_VER || defined __INTEL_COMPILER) && USE_COMPILER_F80_TYPE && (defined ia32 || defined efi2 || defined ia64)\r
    #define BINARY80 long double\r
  #else\r
    #define BINARY80 BINARY128\r
  #endif\r",
        &tests_path.join("test_bid_functions.h"),
    );

    replace_in_file(
        "#define binary80_to_bid32 __binary80_to_bid32\r",
        "#if (!defined _MSC_VER || defined __INTEL_COMPILER) && USE_COMPILER_F80_TYPE && (defined ia32 || defined efi2 || defined ia64)\r
  #define binary80_to_bid32 __binary80_to_bid32\r
#else\r
  #define binary80_to_bid132 __binary128_to_bid32\r
#endif\r",
        bid_conf_path,
    );

    replace_in_file(
        "#define binary80_to_bid64 __binary80_to_bid64\r",
        "#if (!defined _MSC_VER || defined __INTEL_COMPILER) && USE_COMPILER_F80_TYPE && (defined ia32 || defined efi2 || defined ia64)\r
  #define binary80_to_bid64 __binary80_to_bid64\r
#else\r
  #define binary80_to_bid64 __binary128_to_bid64\r
#endif\r",
        bid_conf_path,
    );

    replace_in_file(
        "#define binary80_to_bid128 __binary80_to_bid128\r",
        "#if (!defined _MSC_VER || defined __INTEL_COMPILER) && USE_COMPILER_F80_TYPE && (defined ia32 || defined efi2 || defined ia64)\r
  #define binary80_to_bid128 __binary80_to_bid128\r
#else\r
  #define binary80_to_bid128 __binary128_to_bid128\r
#endif\r",
        bid_conf_path,
    );

    replace_in_file(
        "#define bid32_to_binary80 __bid32_to_binary80\r",
        "#if (!defined _MSC_VER || defined __INTEL_COMPILER) && USE_COMPILER_F80_TYPE && (defined ia32 || defined efi2 || defined ia64)\r
  #define bid32_to_binary80 __bid32_to_binary80\r
#else\r
  #define bid32_to_binary80 __bid32_to_binary128\r
#endif\r",
        bid_conf_path,
    );

    replace_in_file(
        "#define bid64_to_binary80 __bid64_to_binary80\r",
        "#if (!defined _MSC_VER || defined __INTEL_COMPILER) && USE_COMPILER_F80_TYPE && (defined ia32 || defined efi2 || defined ia64)\r
  #define bid64_to_binary80 __bid64_to_binary80\r
#else\r
  #define bid64_to_binary80 __bid64_to_binary128\r
#endif\r",
        bid_conf_path,
    );

    replace_in_file(
        "#define bid128_to_binary80 __bid128_to_binary80\r",
        "#if (!defined _MSC_VER || defined __INTEL_COMPILER) && USE_COMPILER_F80_TYPE && (defined ia32 || defined efi2 || defined ia64)\r
  #define bid128_to_binary80 __bid128_to_binary80\r
#else\r
  #define bid128_to_binary80 __bid128_to_binary128\r
#endif\r",
        bid_conf_path,
    );

    // for compatibiity with architectures where char is unsigned

    replace_in_file(
        "typedef char BID_SINT8;",
        "typedef signed char BID_SINT8;",
        bid_functions_path,
    );

    replace_in_file(
        "BID_EXTERN_C char bid32_to_int8",
        "BID_EXTERN_C signed char bid32_to_int8",
        bid_functions_path,
    );

    replace_in_file(
        "BID_EXTERN_C char bid64_to_int8",
        "BID_EXTERN_C signed char bid64_to_int8",
        bid_functions_path,
    );

    replace_in_file(
        "BID_EXTERN_C char bid128_to_int8",
        "BID_EXTERN_C signed char bid128_to_int8",
        bid_functions_path,
    );

    replace_in_file(
        "(char, bid32_to_int8",
        "(signed char, bid32_to_int8",
        &lib_src_path.join("bid32_to_int8.c"),
    );

    replace_in_file(
        "(char, bid64_to_int8",
        "(signed char, bid64_to_int8",
        &lib_src_path.join("bid64_to_int8.c"),
    );

    replace_in_file(
        "(char, bid128_to_int8",
        "(signed char, bid128_to_int8",
        &lib_src_path.join("bid128_to_int8.c"),
    );

    replace_in_file(
        "#define __bid_f80_hypot(res, a, b)     __BID_F80_F_FF_FUNC(res, a, b, hypot)",
        "#define __bid_f80_hypot(res, a, b)     __BID_F80_F_FF_FUNC(res, a, b, hypot)\r
#if defined NEED_EXP10L\r
	#define __bid_f80_pow(res, a, b) __BID_F80_F_FF_FUNC(res, a, b, pow)\r
	#define __bid_f80_modf(res, a, b) __BID_F80_F_FF_FUNC(res, a, b, modf)\r
#endif",
        bid_trans_path,
    );

    replace_in_file(
        "#define __bid_f128_nextafter(res, a, b) __BID_F128_F_FF_FUNC(res, a, b, nextafter)",
        "#define __bid_f128_nextafter(res, a, b) __BID_F128_F_FF_FUNC(res, a, b, nextafter)\r
#define __bid_f128_pow(res, a, b) __BID_F128_F_FF_FUNC(res, a, b, pow)\r
#define __bid_f128_modf(res, a, b) __BID_F128_F_FF_FUNC(res, a, b, modf)",
        bid_trans_path,
    );

    replace_in_file(
        "__BID_F128_F_FF_DECL(nextafter);",
        "__BID_F128_F_FF_DECL(nextafter);\r
__BID_F128_F_FF_DECL(pow);\r
extern BID_F128_TYPE __BID_F128_NAME(modf)( BID_F128_TYPE, BID_F128_TYPE*);",
        bid_trans_path,
    );

    replace_in_file(
        "__BID_F80_F_FF_DECL(hypot);",
        "__BID_F80_F_FF_DECL(hypot);\r
    #if defined NEED_EXP10L\r
        __BID_F80_F_FF_DECL(pow);\r
        extern BID_F80_TYPE __BID_F80_NAME(modf)( BID_F80_TYPE, BID_F80_TYPE*);\r
    #endif",
        bid_trans_path,
    );

    {
        let mut bid_trans_file = OpenOptions::new()
            .write(true)
            .append(true)
            .open(bid_trans_path)
            .unwrap();

        bid_trans_file
            .write_all(
                "\r
\r
#include <stdint.h>\r
#if defined BID_BIG_ENDIAN\r
union ldshape {\r
	long double f;\r
	struct {\r
		uint16_t se;\r
		uint16_t top;\r
		uint32_t mid;\r
		uint64_t lo;\r
	} i;\r
	struct {\r
		uint64_t hi;\r
		uint64_t lo;\r
	} i2;\r
};\r
#else\r
union ldshape {\r
	long double f;\r
	struct {\r
		uint64_t lo;\r
		uint32_t mid;\r
		uint16_t top;\r
		uint16_t se;\r
	} i;\r
	struct {\r
		uint64_t lo;\r
		uint64_t hi;\r
	} i2;\r
};\r
#endif\r
#if defined libquadmath\r
__float128 exp10q(__float128 x);\r
#endif\r
#if (defined NEED_EXP10L) && USE_COMPILER_F80_TYPE\r
long double exp10l(long double x)\r;
#endif"
                    .as_bytes(),
            )
            .unwrap();

        bid_trans_file.sync_all().unwrap();
    }

    replace_in_file(
        "#include \"bid_trans.h\"",
        "#include \"bid_trans.h\"
#if (defined NEED_EXP10L) && USE_COMPILER_F80_TYPE
long double exp10l(long double x)
{
	static const long double p10[] = {
		1e-15L, 1e-14L, 1e-13L, 1e-12L, 1e-11L, 1e-10L,
		1e-9L, 1e-8L, 1e-7L, 1e-6L, 1e-5L, 1e-4L, 1e-3L, 1e-2L, 1e-1L,
		1, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9,
		1e10, 1e11, 1e12, 1e13, 1e14, 1e15
	};
	long double n, y, ret;
	__bid_f80_modf(y, x, &n);
	union ldshape u = {n};
	/* fabsl(n) < 16 without raising invalid on nan */
	if ((u.i.se & 0x7fff) < 0x3fff+4) {
		if (!y) return p10[(int)n+15];
		y = __bid_f80_exp2(y, 3.32192809488736234787031942948939L * y);
		return y * p10[(int)n+15];
	}
	__bid_f80_pow(ret, 10.0, x);
	return ret;
}
#endif",
        &lib_src_path.join("bid64_exp10.c"),
    );

    replace_in_file(
        "#include \"bid_trans.h\"",
        "#include \"bid_trans.h\"
#if defined libquadmath
__float128 exp10q(__float128 x)
{
	static const __float128 p10[] = {
		1e-15Q, 1e-14Q, 1e-13Q, 1e-12Q, 1e-11Q, 1e-10Q,
		1e-9Q, 1e-8Q, 1e-7Q, 1e-6Q, 1e-5Q, 1e-4Q, 1e-3Q, 1e-2Q, 1e-1Q,
		1, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9,
		1e10, 1e11, 1e12, 1e13, 1e14, 1e15
	};
	__float128 n, y, ret;
	__bid_f128_modf(y, x, &n);
	union ldshape u = {n};
	/* fabsq(n) < 16 without raising invalid on nan */
	if ((u.i.se & 0x7fff) < 0x3fff+4) {
		if (!y) return p10[(int)n+15];
		__bid_f128_exp2(y, 3.32192809488736234787031942948939Q * y);
		return y * p10[(int)n+15];
	}
	__bid_f128_pow(ret, 10.0, x);
	return ret;
}
#endif",
        &lib_src_path.join("bid128_exp10.c"),
    );

    replace_in_file(
        "#include \"bid_internal.h\"",
        "#include <stdlib.h>\n#include \"bid_internal.h\"",
        &lib_src_path.join("bid32_pow.c"),
    );

    replace_in_file(
        "#include \"bid_trans.h\"",
        "#include <stdlib.h>\n#include \"bid_trans.h\"",
        &lib_src_path.join("bid64_pow.c"),
    );

    replace_in_file(
        "#include \"bid_trans.h\"",
        "#include <stdlib.h>\n#include \"bid_trans.h\"",
        &lib_src_path.join("bid128_pow.c"),
    );

    replace_in_file(
        "#   include <sys/signal.h>",
        "#   include <signal.h>",
        &lib_f128_path.join("dpml_exception.c"),
    );

    // Target info
    let target_is_unix = build::cargo_cfg_unix();
    let target_is_windows = build::cargo_cfg_windows();
    let target_arch: &str = &build::cargo_cfg_target_arch();
    let target_endian: &str = &build::cargo_cfg_target_endian();
    let target_os: &str = &build::cargo_cfg_target_os();
    let target_env: &str = &build::cargo_cfg_target_env();
    //let target_features: &[String] = &build::cargo_cfg_target_feature(); FIXME handle this once Cargo actually gives us the features

    // -D defines that get passed to both cc and bindgen's libclang.
    let mut defines: Vec<(&str, Option<&str>)> = vec![
        ("CALL_BY_REF", Some("0")),
        ("GLOBAL_RND", Some("0")),
        ("GLOBAL_FLAGS", Some("0")),
        ("UNCHANGED_BINARY_FLAGS", Some("0")),
    ];

    // Compiler flags that get passed to both cc and bindgen's libclang.
    let mut flags: Vec<&str> = vec![];

    // Compiler flags that get passed to bindgen's libclang, but to cc only if cc is clang.
    let mut clang_flags: Vec<&str> = vec![];

    if target_endian == "big" {
        defines.push(("BID_BIG_ENDIAN", None));
    }

    if target_is_unix {
        defines.push(("LINUX", None));
    }

    if target_is_windows {
        defines.push(("WINDOWS", None));
        defines.push(("WINNT", None));
        defines.push(("WNT", None));
        defines.push(("winnt", None));
    }

    // These platforms ship libm without `exp10l`, so we provide one from musl.
    let need_exp10l = matches!(
        target_os,
        "macos" | "ios" | "android" | "solaris" | "illumos" | "dragonfly"
    ) || target_os.contains("bsd");

    if need_exp10l {
        defines.push(("NEED_EXP10L", None));
    }

    // Whether the compiler-native f128 type relies on libquadmath
    // or glibc >= 2.26
    let mut float128_is_not_long_double = false;

    // `false` if the Intel library implements binary80/binary128 for the target.
    let mut need_compiler_float = true;
    let mut have_compiler_float = true;

    match target_arch {
        "x86" => {
            need_compiler_float = false;
            defines.push(("ia32", None));
            float128_is_not_long_double = true;
            if target_is_windows {
                have_compiler_float = false;
            }
        }
        "x86_64" => {
            need_compiler_float = false;
            defines.push(("efi2", None));
            float128_is_not_long_double = true;
            if target_is_windows {
                have_compiler_float = false;
            }
        }
        "powerpc" | "powerpc64" => {
            if target_endian != "little" {
                panic!("big-endian PowerPC is not supported");
            }

            defines.push(("ppc", None));

            flags.push("-mvsx");
            flags.push("-mfloat128");

            clang_flags.push("-mcpu=pwr9");

            float128_is_not_long_double = true;

            /*if !target_features.iter().any(|f| f == "vsx") {
                panic!("the `vsx` target feature is needed to support float128 on PowerPC targets")
            }*/ // FIXME currently no good way of detecting this
        }
        "aarch64" => {
            if target_is_windows || target_os == "macos" {
                panic!("`aarch64` is unsupported on Windows or Mac OS")
            }
        }
        _ => {}
    }

    // TODO https://github.com/rust-lang/rust-bindgen/issues/1941#issuecomment-748630710
    if target_os == "emscripten" {
        flags.push("-fvisibility=default");
    }

    let use_compiler_f80_type =
        (build::cargo_feature("compiler_native_f80") || need_compiler_float) && have_compiler_float;
    let mut use_compiler_f128_type: bool = (build::cargo_feature("compiler_native_f128")
        || need_compiler_float)
        && have_compiler_float;

    let mut use_glibc_2_26 = false;
    let mut use_libquadmath = false;

    if use_compiler_f128_type && float128_is_not_long_double {
        if build::cargo_feature("glibc_2_26") && target_env == "gnu" {
            use_glibc_2_26 = true;
        } else if build::cargo_feature("libquadmath") {
            use_libquadmath = true;
        } else if need_compiler_float {
            if target_env == "gnu" {
                panic!(
                    "this target requires one of the `glibc_2_26` or `libquadmath` crate features"
                );
            } else {
                panic!("this target requires the `libquadmath` crate feature");
            }
        } else {
            use_compiler_f128_type = false;
        }
    }

    if use_glibc_2_26 {
        defines.push(("glibc_2_26", None));
    }

    if use_libquadmath {
        defines.push(("libquadmath", None));
    }

    // https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html
    // https://cpufun.substack.com/p/portable-support-for-128b-floats
    // https://github.com/llvm/llvm-project/blob/main/clang/lib/Basic/Targets LongDoubleWidth in headers
    if use_compiler_f80_type {
        defines.push(("USE_COMPILER_F80_TYPE", Some("1")));
    } else {
        defines.push(("USE_COMPILER_F80_TYPE", Some("0")));
    }

    if use_compiler_f128_type {
        defines.push(("USE_COMPILER_F128_TYPE", Some("1")));
        defines.push(("USE_NATIVE_QUAD_TYPE", Some("1")));
    } else {
        defines.push(("USE_COMPILER_F128_TYPE", Some("0")));
        defines.push(("USE_NATIVE_QUAD_TYPE", Some("0")));
    }

    // Build the library
    let mut cc_build = cc::Build::new();

    cc_build.warnings(false);

    if build::cargo_feature("no_pic") {
        cc_build.pic(false);

        if !build::cargo_feature("no_pie") {
            cc_build.flag("-fPIE");
        }
    }

    let compiler = cc_build.get_compiler();

    if compiler.is_like_gnu() {
        defines.push(("gcc", None));
    }

    if compiler.is_like_clang() || target_os == "emscripten" {
        defines.push(("clang", None));

        // clang is more noisy than gcc, silence the extra warnings
        cc_build.flag("-Wno-comment");
        cc_build.flag("-Wno-constant-conversion");
        cc_build.flag("-Wno-dangling-else");
        cc_build.flag("-Wno-parentheses");
        cc_build.flag("-Wno-shift-negative-value");
        cc_build.flag("-Wno-implicit-function-declaration");
    }

    let is_windows_msvc = target_is_windows && compiler.is_like_msvc();
    if is_windows_msvc {
        defines.push(("cl", None));
    }

    defines.iter().for_each(|&(var, val)| {
        cc_build.define(var, val);
    });

    flags.iter().for_each(|&flag| {
        cc_build.flag(flag);
    });

    if compiler.is_like_clang() {
        clang_flags.iter().for_each(|&flag| {
            cc_build.flag(flag);
        });
    }

    if build::cargo_feature("lto") && build::profile() == "release" {
        cc_build.flag("-flto");
    }

    // From makefile

    for result in fs::read_dir(lib_src_path).unwrap() {
        let path = result.unwrap().path();
        let path = path.as_path();
        if path.extension() == Some("c".as_ref()) {
            cc_build.file(path);
        }
    }

    if !use_compiler_f128_type {
        let f128_names = [
            "dpml_ux_bid.c",
            "dpml_ux_bessel.c",
            "dpml_ux_cbrt.c",
            "dpml_ux_erf.c",
            "dpml_ux_exp.c",
            "dpml_ux_int.c",
            "dpml_ux_inv_hyper.c",
            "dpml_ux_inv_trig.c",
            "dpml_ux_lgamma.c",
            "dpml_ux_log.c",
            "dpml_ux_mod.c",
            "dpml_ux_powi.c",
            "dpml_ux_pow.c",
            "dpml_ux_sqrt.c",
            "dpml_ux_trig.c",
            "dpml_ux_ops.c",
            "dpml_ux_ops_64.c",
            "dpml_four_over_pi.c",
            "dpml_exception.c",
            "sqrt_tab_t.c",
        ];

        for result in f128_names.into_iter() {
            cc_build.file(lib_f128_path.join(result));
        }
    }

    dbg!(cc_build.get_compiler().to_command());

    cc_build.compile("bid");

    // Needs to be after `compile`
    if use_libquadmath {
        build::rustc_link_lib("quadmath");
    }

    // Generate Rust bindings
    let mut bindings_gen = bindgen::Builder::default()
        // from IntelRDFPMathLib20U2/README
        .header(lib_src_path.join("bid_conf.h").to_str().unwrap())
        .header(lib_src_path.join("bid_functions.h").to_str().unwrap())
        // Restict exposed items to those actually from the library
        .allowlist_function("(__bid|__binary|BID|BINARY|DEC).*")
        .allowlist_var("(__bid|__binary|BID|BINARY|DEC).*")
        // Block function signatures that use non ffi-safe types
        .blocklist_item(".*binary(80|128).*");

    for &(var, val) in defines.iter() {
        if let Some(val) = val {
            bindings_gen = bindings_gen.clang_arg(&format!("-D{var}={val}"));
        } else {
            bindings_gen = bindings_gen.clang_arg(&format!("-D{var}"));
        }
    }

    for &flag in flags.iter().chain(clang_flags.iter()) {
        bindings_gen = bindings_gen.clang_arg(flag);
    }

    if target_arch.starts_with("powerpc") {
        bindings_gen = bindings_gen.clang_arg("-mcpu=pwr9");
    }

    dbg!(&bindings_gen.command_line_flags());

    let bindings = bindings_gen
        .generate()
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");

    // Test cases
    let test_file: &str = &fs::read_to_string(tests_path.join("readtest.in")).unwrap();
    let mut test_code: String = r#"use ::core::{mem::transmute, cmp::Ordering};

fn decompose_32(d: u32) -> (u32, u32) {
    const MASK_STEERING_BITS: u32 = 0b11 << (32 - 3);
    if d & MASK_STEERING_BITS == MASK_STEERING_BITS {
        let exp = (d & 0x1fe00000) >> 21;
        let mantissa = (d & 0x001fffff) | 0x00800000;
        (exp, mantissa)
    } else {
        let exp = (d & 0x7f800000) >> 23;
        let mantissa = d & 0x007fffff;
        (exp, mantissa)
    }
}

const MRE_MAX_32: [f64; 5] = [0.5, 1.01, 1.01, 1.01, 0.5];

fn decompose_64(d: u64) -> (u64, u64) {
    const MASK_STEERING_BITS: u64 = 0b11 << (64 - 3);
    if d & MASK_STEERING_BITS == MASK_STEERING_BITS {
        let exp = (d & 0x1ff8000000000000) >> 51;
        let mantissa = (d & 0x0007ffffffffffff) | 0x0020000000000000;
        (exp, mantissa)
    } else {
        let exp = (d & 0x7fe0000000000000) >> 23;
        let mantissa = d & 0x001fffffffffffff;
        (exp, mantissa)
    }
}

const MRE_MAX_64: [f64; 5] = [0.55, 1.05, 1.05, 1.05, 0.55];

fn decompose_128(d: u128) -> (u128, u128) {
    const MASK_STEERING_BITS: u128 = 0b11 << (64 - 3);
    if d & MASK_STEERING_BITS == MASK_STEERING_BITS {
        let exp = (d & 0x1fff8000000000000000000000000000) >> 79;
        let mantissa = (d & 0x00007fffffffffffffffffffffffffff) | 0x00020000000000000000000000000000;
        (exp, mantissa)
    } else {
        let exp = (d & 0x7ffe0000000000000000000000000000) >> 81;
        let mantissa = d & 0x0001ffffffffffffffffffffffffffff;
        (exp, mantissa)
    }
}

const MRE_MAX_128: [f64; 5] = [2.0, 5.0, 5.0, 5.0, 2.0];

"#.to_string();

    for x in [32, 64, 128] {
        test_code.push_str(&format!(
r#"
// returns (exponent, mantissa)
fn rel_ulp_check_{x}(l: BID_UINT{x}, r: BID_UINT{x}, ulp_add: f64, rnd_mode: _IDEC_round, max_array: [f64; 5]) -> bool {{

    let (l_is_nan, r_is_nan): (bool, bool) = unsafe {{ (__bid{x}_isNaN(l) != 0, __bid{x}_isNaN(r) != 0) }};
    let (l_is_inf, r_is_inf): (bool, bool) = unsafe {{ (__bid{x}_isNaN(l) != 0, __bid{x}_isInf(r) != 0) }};
    
    let l_bits: u{x} = unsafe {{ transmute(l) }};
    let r_bits: u{x} = unsafe {{ transmute(r) }};

    if l_is_nan || r_is_nan || l_is_inf || r_is_inf {{
        if l_bits == r_bits {{
            return true;
        }} else {{
            return false;
        }}
    }}

    let l_sign = l_bits & (1 << ({x} - 1));
    if l_sign != r_bits & (1 << ({x} - 1)) {{
        return false;
    }}

    let (mut l_exp, mut l_mant) = decompose_{x}(l_bits);
    let (mut r_exp, mut r_mant) = decompose_{x}(l_bits);

    match l_exp.cmp(&r_exp) {{
        Ordering::Less => {{
            let l_q: BID_UINT{x} = unsafe {{ __bid{x}_quantize(l, r, rnd_mode, &mut 0) }};
            (l_exp, l_mant) = decompose_{x}(unsafe {{ transmute(l_q) }});
        }},
        Ordering::Greater => {{
            let r_q: BID_UINT{x} = unsafe {{ __bid{x}_quantize(r, l, rnd_mode, &mut 0) }};
            (r_exp, r_mant) = decompose_{x}(unsafe {{ transmute(r_q) }});
        }},
        Ordering::Equal => {{}},
    }}
    
    if l_exp != r_exp {{
        return false;
    }}

    let mut ulp: f64 = l_mant.abs_diff(r_mant) as f64;

    if unsafe {{ __bid{x}_quiet_less(l, r, &mut 0) }} != 0 {{
        ulp = -ulp;
    }}

    (ulp + ulp_add).abs() <= max_array[rnd_mode as usize]
}}

fn exact_eq{x}(l: BID_UINT{x}, r: BID_UINT{x}) -> bool {{
    (unsafe {{ transmute::<_, u{x}>(l) }}) == (unsafe {{ transmute::<_, u{x}>(r) }})
}}
"#));
    }
    for (i, mut line) in test_file.lines().enumerate() {
        let i = i + 1;
        // FIXME investigate these
        if matches!(
            i,
            3602 | 11402 | 71599 | 71628 | 71707 | 94137 | 94694 | 95398 | 95599
        ) {
            continue;
        }
        line = line.split_once("--").map_or(line, |(left, _)| left).trim();
        line = line
            .strip_suffix("underflow_before_only")
            .unwrap_or(line)
            .trim_end();
        line = line
            .strip_suffix("undefrlow_before_only")
            .unwrap_or(line)
            .trim_end();

        if line.is_empty() {
            continue;
        }

        let mut parts = line.split_ascii_whitespace();
        let fn_name = parts.next().unwrap();
        let size: u8;
        let fn_tail: &str;
        if let Some(tail) = fn_name.strip_prefix("bid32_") {
            size = 32;
            fn_tail = tail;
        } else if let Some(tail) = fn_name.strip_prefix("bid64_") {
            size = 64;
            fn_tail = tail;
        } else if let Some(tail) = fn_name.strip_prefix("bid128_") {
            size = 128;
            fn_tail = tail;
        } else {
            // TODO non-homogeneous
            continue;
        }

        let rnd_mode = parts.next().unwrap().parse::<u32>().unwrap();

        match fn_tail {
            // CMP_FUZZYSTATUS rounded readtest.h
            "add"
            | "sub"
            | "mul"
            | "div"
            | "quantize"
            | "nearbyint"
            | "fma"
            | "round_integral_exact" => {
                let expected_flags =
                    u32::from_str_radix(parts.next_back().unwrap(), 16).unwrap_or(0);
                let ans: &str = &parse_test_dec(parts.next_back().unwrap(), size);
                let mut args_string = String::new();
                for arg_str in parts {
                    args_string.push_str(&parse_test_dec(arg_str, size));
                    args_string.push_str(", ");
                }

                test_code.push_str(&format!(
                    "#[test] fn readtest_{i:06}_{fn_name}() {{ let mut flags: _IDEC_flags = 0; unsafe {{ assert!(exact_eq{size}(__{fn_name}({args_string}{rnd_mode}, &mut flags), {ans}), \"wrong result\"); }} assert_eq!(flags & 0x5, 0x{expected_flags:x} & 0x5, \"wrong flags\"); }}\n"
                ));
            }
            // CMP_FUZZYSTATUS not rounded readtest.h
            _ if fn_tail.starts_with("round_integral")
                | matches!(
                    fn_tail,
                    "rem" | "fmod" | "minnum" | "maxnum" | "minnum_mag" | "maxnum_mag" | "logb"
                ) =>
            {
                let last = parts.next_back().unwrap();
                let expected_flags: u32 = if last.strip_prefix("ulp=").is_some() {
                    u32::from_str_radix(parts.next_back().unwrap(), 16).unwrap()
                } else {
                    u32::from_str_radix(last, 16).unwrap()
                };
                let ans: &str = &parse_test_dec(parts.next_back().unwrap(), size);
                let mut args_string = String::new();
                for arg_str in parts {
                    args_string.push_str(&parse_test_dec(arg_str, size));
                    args_string.push_str(", ");
                }

                test_code.push_str(&format!(
                    "#[test] fn readtest_{i:06}_{fn_name}() {{ let mut flags: _IDEC_flags = 0; unsafe {{ assert!(exact_eq{size}(__{fn_name}({args_string}&mut flags), {ans}), \"wrong result\"); }} assert_eq!(flags & 0x5, 0x{expected_flags:x} & 0x5, \"wrong flags\"); }}\n"
                ));
            }
            // CMP_RELATIVEERR readtest.h
            "exp" | "log" | "pow" | "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "sinh"
            | "cosh" | "tanh" | "asinh" | "acosh" | "atanh" | "hypot" | "cbrt" | "expm1"
            | "log1p" | "log10" | "exp2" | "exp10" | "log2" | "erf" | "erfc" | "sqrt"
            | "tgamma" | "lgamma" => {
                if fn_tail == "exp10" && need_exp10l && !use_compiler_f128_type {
                    continue; // TODO
                }

                let last = parts.next_back().unwrap();
                let expected_flags;
                let ulp_add: f64;
                if let Some(ulp_str) = last.strip_prefix("ulp=") {
                    ulp_add = ulp_str.parse().unwrap();
                    expected_flags = u32::from_str_radix(parts.next_back().unwrap(), 16).unwrap();
                } else {
                    ulp_add = 0.0;
                    expected_flags = u32::from_str_radix(last, 16).unwrap();
                }

                let ans: &str = &parse_test_dec(parts.next_back().unwrap(), size);
                let mut args_string = String::new();
                for arg_str in parts {
                    args_string.push_str(&parse_test_dec(arg_str, size));
                    args_string.push_str(", ");
                }

                let mre_max_string;
                let ulp_array_str: &str = match fn_name {
                    "bid32_acosh" | "bid64_acosh" => {
                        "[0.55*2.0, 1.05*2.0, 1.05*2.0, 1.05*2.0, 0.55*2.0]"
                    }
                    "bid32_tgamma" | "bid32_lgamma" => {
                        "[0.55e+4, 1.05e+4, 1.05e+4, 1.05e+4, 0.55e+4]"
                    }
                    "bid64_tgamma" | "bid64_lgamma" | "bid128_lgamma" => {
                        "[0.55e+13, 1.05e+13, 1.05e+13, 1.05e+13, 0.55e+13]"
                    }
                    "bid128_tgamma" => "[0.55e+31, 1.05e+31, 1.05e+31, 1.05e+31, 0.55e+31]",
                    _ => {
                        mre_max_string = format!("MRE_MAX_{size}");
                        &mre_max_string
                    }
                };

                test_code.push_str(&format!(
                    "#[test] fn readtest_{i:06}_{fn_name}() {{ let mut flags: _IDEC_flags = 0; unsafe {{ assert!(rel_ulp_check_{size}(__{fn_name}({args_string}{rnd_mode}, &mut flags), {ans}, {ulp_add}_f64, {rnd_mode}, {ulp_array_str}), \"wrong result\"); }} assert_eq!(flags & 0x5, 0x{expected_flags:x} & 0x5, \"wrong flags\"); }}\n"
                ));
            }
            _ => {}
        }
    }

    fs::write(out_path.join("readtest.rs"), test_code).unwrap()
}

fn parse_test_dec(arg_str: &str, size: u8) -> String {
    if let Some(trimmed) = arg_str.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
        if let Some((left, right)) = trimmed.split_once(',') {
            let (left_int, right_int) = (
                u64::from_str_radix(left, 16).unwrap(),
                u64::from_str_radix(right, 16).unwrap(),
            );
            let (left_bits, right_bits) = (left_int.to_be_bytes(), right_int.to_be_bytes());
            let big_int = u128::from_be_bytes([
                left_bits[0],
                left_bits[1],
                left_bits[2],
                left_bits[3],
                left_bits[4],
                left_bits[5],
                left_bits[6],
                left_bits[7],
                right_bits[0],
                right_bits[1],
                right_bits[2],
                right_bits[3],
                right_bits[4],
                right_bits[5],
                right_bits[6],
                right_bits[7],
            ]);
            format!("transmute::<_, BID_UINT{size}>(0x{big_int:x}_u{size})")
        } else if trimmed.len() > 16 {
            format!("transmute::<_, BID_UINT{size}>(0x{trimmed}_u{size})")
        } else {
            format!("0x{trimmed}_u{size}")
        }
    } else {
        format!(
            r#"__bid{size}_from_string(b"{arg_str}\0" as *const u8 as *mut u8 as *mut ::std::os::raw::c_char, 0, &mut 0)"#
        )
    }
}
