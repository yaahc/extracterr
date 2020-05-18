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

Helpers for bundling context with errors and later extracting said context thru `dyn Error`
trait objects.

The primary purpose of this crate is to pass context to error reporters through `dyn Error`
trait objects. This is useful for information that may need to be captured by leaf errors but
which doesn't belong in any single error's message. Backtraces, http status codes, and help
messages are all examples of context that one might wish to pass directly to an error reporter
rather than printing in the chain of errors.

## Setup

```toml
[dependencies]
extracterr = "0.1"
```

## TLDR Example

```rust
use backtrace::Backtrace;
use std::error::Error;
use extracterr::{Bundle, Bundled, Extract};

#[derive(Debug, thiserror::Error)]
#[error("Example Error")]
struct ExampleError;

let error = ExampleError;

// Capture a backtrace via `Default` and `From`
let error: Bundled<_, Backtrace> = error.into();

// Convert it to a trait object to throw away type information
let error: Box<dyn Error + Send + Sync + 'static> = error.into();

// first error in chain is the unerased version of the error `Bundled<ExampleError, Backtrace>`
assert!(error.downcast_ref::<Bundled<ExampleError, Backtrace>>().is_some());
assert_eq!("Example Error", error.to_string());
assert!(error.extract::<Backtrace>().is_none());

// Move to the next error in the chain
let error = error.source().unwrap();

// The second error in the chain is the erased version `Bundled<Erased, Backtrace>` which now
// works with downcasting, letting us access the bundled context
let backtrace = error.extract::<Backtrace>();
assert!(backtrace.is_some());

// The Display / Debug impls of the fake error that contains the bundled context print the
// context's type_name
assert_eq!(error.to_string(), std::any::type_name::<Backtrace>());
```

## Details

The main type provided by this library is the `Bundled` type, which bundles an error and a
context type into a new error. This type can be constructed either via `From+Default` or
[`Bundle`], for more details check out the docs on [`Bundled`].

This type works best with the error kind pattern, as seen in `std::io::Error`:

```rust
use backtrace::Backtrace;
use extracterr::{Bundle, Bundled};

#[derive(Debug, thiserror::Error)]
#[error(transparent)]
struct Error {
    kind: Bundled<Kind, Backtrace>,
}

#[derive(Debug, thiserror::Error, Clone, Copy)]
enum Kind {
    #[error("could not enqueue item")]
    Queue,
    #[error("could not dequeue item")]
    Dequeue
}

impl Error {
    fn kind(&self) -> Kind {
        *self.kind.inner()
    }
}

impl From<Kind> for Error {
    fn from(kind: Kind) -> Self {
        Self { kind: Bundled::from(kind) }
    }
}

impl From<Bundled<Kind, Backtrace>> for Error {
    fn from(kind: Bundled<Kind, Backtrace>) -> Self {
        Self { kind }
    }
}

fn queue() -> Result<(), Error> {
    Err(Kind::Queue)?
}

fn dequeue() -> Result<(), Error> {
    Err(Kind::Dequeue).bundle(Backtrace::new())?
}

use extracterr::Extract;

let error = dequeue().unwrap_err();

// Convert it to a trait object to throw away type information
let error: Box<dyn std::error::Error + Send + Sync + 'static> = error.into();

// first error in chain is the unerased version of the error `Bundled<ExampleError, Backtrace>`
assert!(error.downcast_ref::<Error>().is_some());
assert_eq!("could not dequeue item", error.to_string());
assert!(error.extract::<Backtrace>().is_none());

// Move to the next error in the chain
let error = error.source().unwrap();

// The second error in the chain is the erased version `Bundled<Erased, Backtrace>` which now
// works with downcasting, letting us access the bundled context
let backtrace = error.extract::<Backtrace>();
assert!(backtrace.is_some());

// The Display / Debug impls of the fake error that contains the bundled context print the
// context's type_name
assert_eq!(error.to_string(), std::any::type_name::<Backtrace>());
```

Once context has been bundled into a chain of errors it can then be extracted back out via the
[`Extract`] trait. Check out the source code of [`stable-eyre`] for a simple example of
idiomatic usage of `Extract` in an error reporter.

[`Bundle`]: trait.Bundle.html
[`Bundled`]: struct.Bundled.html
[`Extract`]: trait.Extract.html
[`stable-eyre`]: https://github.com/yaahc/stable-eyre

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
