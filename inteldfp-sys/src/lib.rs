#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![doc = concat!("```text\n", include_str!(concat!(env!("OUT_DIR"), "/IntelRDFPMathLib20U2/README")), "\n```")]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

#[cfg(test)]
mod readtest {
    use super::*;
    include!(concat!(env!("OUT_DIR"), "/readtest.rs"));
}

const _: () = {
    if !(::core::mem::size_of::<BID_UINT32>() == 4
        && ::core::mem::size_of::<BID_UINT64>() == 8
        && ::core::mem::size_of::<BID_UINT128>() == 16)
    {
        panic!()
    }
};
