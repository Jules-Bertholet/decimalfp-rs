# `decimalfp-rs`

Decimal floating point arithmetic in Rust, using the
[Intel Decimal Floating-Point Math Library](https://www.intel.com/content/www/us/en/developer/articles/tool/intel-decimal-floating-point-math-library.html).

Conforms to the IEEE 754-2019 decimal floating point standard.

## Example

```
use decimalfp::prelude::*;

let a = d64!(1.0);
let b = d64!(4.7);

let result = a * powi(b, 2);
```