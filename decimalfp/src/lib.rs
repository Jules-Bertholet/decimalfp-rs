use std::{
    ffi::{CStr, CString},
    os::raw::c_char,
};

#[repr(transparent)]
pub struct Decimal32 {
    inner: inteldfp_sys::BID_UINT32,
}

#[repr(transparent)]
pub struct Decimal64 {
    inner: inteldfp_sys::BID_UINT64,
}

#[repr(transparent)]
pub struct Decimal128 {
    inner: inteldfp_sys::BID_UINT128,
}
