#![forbid(unsafe_op_in_unsafe_fn)]
#![warn(/*missing_docs, */missing_debug_implementations, unused_crate_dependencies, clippy::pedantic)]

use core::str::FromStr;
use proc_macro::{Group, Ident, Literal, Span, TokenStream, TokenTree};
use quote::ToTokens;
use std::{ffi::CString, os::raw::c_char};

/// Replace "find" with "replace" in all idents in the `TokenStream`.
#[proc_macro]
pub fn replace(raw_input: TokenStream) -> TokenStream {
    let mut tokens = raw_input.into_iter();

    // (find, replace, $($tt:tt)*)

    // find
    let find_arg: &str = &match tokens.next() {
        Some(TokenTree::Ident(ident)) => ident.to_string(),
        Some(TokenTree::Literal(lit)) => lit.to_string(),
        Some(tree) => return compile_error(tree.span(), "invalid find arg"),
        None => return compile_error(Span::mixed_site(), "missing find arg"),
    };

    // ,
    match tokens.next() {
        Some(TokenTree::Punct(p)) if p.as_char() == ',' => {}
        Some(tree) => return compile_error(tree.span(), "expected comma"),
        None => return compile_error(Span::mixed_site(), "expected comma"),
    }

    // replace
    let replace_arg: &str = &match tokens.next() {
        Some(TokenTree::Ident(ident)) => ident.to_string(),
        Some(TokenTree::Literal(lit)) => lit.to_string(),
        Some(tree) => return compile_error(tree.span(), "invalid replace arg"),
        None => return compile_error(Span::mixed_site(), "missing replace arg"),
    };

    // ,
    match tokens.next() {
        Some(TokenTree::Punct(p)) if p.as_char() == ',' => {}
        Some(tree) => return compile_error(tree.span(), "expected comma"),
        None => return compile_error(Span::mixed_site(), "expected comma"),
    }

    find_and_replace_idents(tokens.collect(), find_arg, replace_arg)
}

fn find_and_replace_idents(stream: TokenStream, find: &str, replace: &str) -> TokenStream {
    stream
        .into_iter()
        .map(|tt| match tt {
            TokenTree::Group(g) => TokenTree::Group(Group::new(
                g.delimiter(),
                find_and_replace_idents(g.stream(), find, replace),
            )),
            TokenTree::Ident(i) => {
                let replace_string: &str = &i.to_string().replace(find, replace);
                if replace_string.chars().next().unwrap().is_numeric() {
                    TokenTree::Literal(Literal::usize_unsuffixed(
                        usize::from_str(replace_string).unwrap(),
                    ))
                } else {
                    TokenTree::Ident(Ident::new(replace_string, i.span()))
                }
            }
            _ => tt,
        })
        .collect()
}

fn compile_error(span: Span, err: &str) -> TokenStream {
    quote::quote_spanned! { span.into() => compile_error!(#err) }
        .to_token_stream()
        .into()
}

#[proc_macro]
pub fn to_bits_32(stream: TokenStream) -> TokenStream {
    to_bits(32, &stream)
}

#[proc_macro]
pub fn to_bits_64(stream: TokenStream) -> TokenStream {
    to_bits(64, &stream)
}

#[proc_macro]
pub fn to_bits_128(stream: TokenStream) -> TokenStream {
    to_bits(128, &stream)
}

// FIXME overflowing
fn to_bits(width: usize, stream: &TokenStream) -> TokenStream {
    const DIGITS: [char; 10] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];

    let literal_string = stream
        .to_string()
        .trim_end_matches(&format!("df{width}"))
        .to_owned()
        .replace('_', "");

    if !literal_string
        .strip_prefix('-')
        .unwrap_or(&literal_string)
        .starts_with(DIGITS)
    {
        return compile_error(Span::call_site(), "invalid decimal literal");
    }

    let literal_str = &literal_string;

    let cstring = CString::new(literal_string.clone()).unwrap();
    let string_ptr = cstring.as_ptr() as *mut c_char;
    let round: inteldfp_sys::_IDEC_round = 0;
    let mut flags: inteldfp_sys::_IDEC_flags = 0;
    let flags_ptr: *mut u32 = &mut flags;

    let (result_literal, is_nan, is_inf, is_negative) = match width {
        32 => {
            let decimal_bits: u32 =
                unsafe { inteldfp_sys::__bid32_from_string(string_ptr, round, flags_ptr) };

            let is_nan = unsafe { inteldfp_sys::__bid32_isNaN(decimal_bits) } != 0;
            let is_inf = unsafe { inteldfp_sys::__bid32_isInf(decimal_bits) } != 0;
            let is_negative = unsafe { inteldfp_sys::__bid32_isSigned(decimal_bits) } != 0;

            (
                Literal::u32_suffixed(decimal_bits),
                is_nan,
                is_inf,
                is_negative,
            )
        }
        64 => {
            let decimal_bits: u64 =
                unsafe { inteldfp_sys::__bid64_from_string(string_ptr, round, flags_ptr) };

            let is_nan = unsafe { inteldfp_sys::__bid64_isNaN(decimal_bits) } != 0;
            let is_inf = unsafe { inteldfp_sys::__bid64_isInf(decimal_bits) } != 0;
            let is_negative = unsafe { inteldfp_sys::__bid64_isSigned(decimal_bits) } != 0;

            (
                Literal::u64_suffixed(decimal_bits),
                is_nan,
                is_inf,
                is_negative,
            )
        }
        128 => {
            let decimal_bits: inteldfp_sys::BID_UINT128 =
                unsafe { inteldfp_sys::__bid128_from_string(string_ptr, round, flags_ptr) };

            let is_nan = unsafe { inteldfp_sys::__bid128_isNaN(decimal_bits) } != 0;
            let is_inf = unsafe { inteldfp_sys::__bid128_isInf(decimal_bits) } != 0;
            let is_negative = unsafe { inteldfp_sys::__bid128_isSigned(decimal_bits) } != 0;

            (
                Literal::u128_suffixed(unsafe { core::mem::transmute(decimal_bits) }),
                is_nan,
                is_inf,
                is_negative,
            )
        }
        _ => panic!("invalid width"),
    };

    if cfg!(not(feature = "allow_overflowing_literals")) && is_inf {
        let infinity_prefix = if is_negative { "NEG_" } else { "" };
        compile_error(
            Span::call_site(),
            &format!(
                r"literal out of range for `Decimal{width}`
= note: enable the `allow_overflowing_literals` crate feature of `decimalfp` to allow this
= note: the literal `d{width}!({literal_str})` does not fit into the type `Decimal{width}` and will be converted to `Decimal{width}::{infinity_prefix}INFINITY`"
            ),
        )
    } else if is_nan {
        compile_error(Span::call_site(), "invalid decimal literal")
    } else {
        TokenTree::Literal(result_literal).into()
    }
}
