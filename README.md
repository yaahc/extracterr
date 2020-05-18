## extracterr

[![Build Status][actions-badge]][actions-url]
[![Latest Version][version-badge]][version-url]
[![Rust Documentation][docs-badge]][docs-url]

[actions-badge]: https://github.com/yaahc/extracterr/workflows/Continuous%20integration/badge.svg
[actions-url]: https://github.com/yaahc/extracterr/actions?query=workflow%3A%22Continuous+integration%22
[version-badge]: https://img.shields.io/crates/v/extracterr.svg
[version-url]: https://crates.io/crates/extracterr
[docs-badge]: https://img.shields.io/badge/docs-latest-blue.svg
[docs-url]: https://docs.rs/extracterr

This crate provides helpers for bundling context with errors and later
extracting said context thru `dyn Error` trait objects.

## Setup

```toml
[dependencies]
extracterr = "0.1"
```

## Example

```rust
use backtrace::Backtrace;
use std::error::Error;
use extracterr::{Bundle, Bundled, Extract};

#[derive(Debug, thiserror::Error)]
#[error("Example Error")]
struct ExampleError;

let error = ExampleError;
let error: Bundled<_, Backtrace> = error.into();
let error: Box<dyn Error + Send + Sync + 'static> = error.into();

// first error in chain should be the error itself
assert_eq!("Example Error", error.to_string());
assert!(error.extract::<Backtrace>().is_none());

let error = error.source().unwrap();
let backtrace = error.extract::<Backtrace>();

assert!(backtrace.is_some());
// The Display / Debug impls of the fake error that contains the bundled context print the
// context's type_name
assert_eq!(error.to_string(), std::any::type_name::<Backtrace>());
```

## Details

## Explanation

## Features

#### License

<sup>
Licensed under either of <a href="LICENSE-APACHE">Apache License, Version
2.0</a> or <a href="LICENSE-MIT">MIT license</a> at your option.
</sup>

<br>

<sub>
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
</sub>
