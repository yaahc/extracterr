//! Helpers for bundling context with errors and later extracting said context thru `dyn Error`
//! trait objects.
//!
//! The primary purpose of this crate is to pass context to error reporters through `dyn Error`
//! trait objects. This is useful for information that may need to be captured by leaf errors but
//! which doesn't belong in any single error's message. Backtraces, http status codes, and help
//! messages are all examples of context that one might wish to pass directly to an error reporter
//! rather than printing in the chain of errors.
//!
//! ## Setup
//!
//! ```toml
//! [dependencies]
//! extracterr = "0.1"
//! ```
//!
//! ## TLDR Example
//!
//! ```rust
//! use backtrace::Backtrace;
//! use std::error::Error;
//! use extracterr::{Bundle, Bundled, Extract};
//!
//! #[derive(Debug, thiserror::Error)]
//! #[error("Example Error")]
//! struct ExampleError;
//!
//! let error = ExampleError;
//!
//! // Capture a backtrace via `Default` and `From`
//! let error: Bundled<_, Backtrace> = error.into();
//!
//! // Convert it to a trait object to throw away type information
//! let error: Box<dyn Error + Send + Sync + 'static> = error.into();
//!
//! // first error in chain is the unerased version of the error `Bundled<ExampleError, Backtrace>`
//! assert!(error.downcast_ref::<Bundled<ExampleError, Backtrace>>().is_some());
//! assert_eq!("Example Error", error.to_string());
//! assert!(error.extract::<Backtrace>().is_none());
//!
//! // Move to the next error in the chain
//! let error = error.source().unwrap();
//!
//! // The second error in the chain is the erased version `Bundled<Erased, Backtrace>` which now
//! // works with downcasting, letting us access the bundled context
//! let backtrace = error.extract::<Backtrace>();
//! assert!(backtrace.is_some());
//!
//! // The Display / Debug impls of the fake error that contains the bundled context print the
//! // context's type_name
//! assert_eq!(error.to_string(), std::any::type_name::<Backtrace>());
//! ```
//!
//! ## Details
//!
//! The main type provided by this library is the `Bundled` type, which bundles an error and a
//! context type into a new error. This type can be constructed either via `From+Default` or
//! [`Bundle`], for more details check out the docs on [`Bundled`].
//!
//! This type works best with the error kind pattern, as seen in `std::io::Error`:
//!
//! ```rust
//! use backtrace::Backtrace;
//! use extracterr::{Bundle, Bundled};
//!
//! #[derive(Debug, thiserror::Error)]
//! #[error(transparent)]
//! struct Error {
//!     kind: Bundled<Kind, Backtrace>,
//! }
//!
//! #[derive(Debug, thiserror::Error, Clone, Copy)]
//! enum Kind {
//!     #[error("could not enqueue item")]
//!     Queue,
//!     #[error("could not dequeue item")]
//!     Dequeue
//! }
//!
//! impl Error {
//!     fn kind(&self) -> Kind {
//!         *self.kind.inner()
//!     }
//! }
//!
//! impl From<Kind> for Error {
//!     fn from(kind: Kind) -> Self {
//!         Self { kind: Bundled::from(kind) }
//!     }
//! }
//!
//! impl From<Bundled<Kind, Backtrace>> for Error {
//!     fn from(kind: Bundled<Kind, Backtrace>) -> Self {
//!         Self { kind }
//!     }
//! }
//!
//! fn queue() -> Result<(), Error> {
//!     Err(Kind::Queue)?
//! }
//!
//! fn dequeue() -> Result<(), Error> {
//!     Err(Kind::Dequeue).bundle(Backtrace::new())?
//! }
//!
//! use extracterr::Extract;
//!
//! let error = dequeue().unwrap_err();
//!
//! // Convert it to a trait object to throw away type information
//! let error: Box<dyn std::error::Error + Send + Sync + 'static> = error.into();
//!
//! assert!(error.downcast_ref::<Error>().is_some());
//! assert_eq!("could not dequeue item", error.to_string());
//! assert!(error.extract::<Backtrace>().is_none());
//!
//! // Move to the next error in the chain
//! let error = error.source().unwrap();
//!
//! let backtrace = error.extract::<Backtrace>();
//! assert!(backtrace.is_some());
//! ```
//!
//! Once context has been bundled into a chain of errors it can then be extracted back out via the
//! [`Extract`] trait. Check out the source code of [`stable-eyre`] for a simple example of
//! idiomatic usage of `Extract` in an error reporter.
//!
//! [`Bundle`]: trait.Bundle.html
//! [`Bundled`]: struct.Bundled.html
//! [`Extract`]: trait.Extract.html
//! [`stable-eyre`]: https://github.com/yaahc/stable-eyre
#![doc(html_root_url = "https://docs.rs/extracterr/0.1.1")]
#![warn(
    missing_debug_implementations,
    missing_docs,
    missing_doc_code_examples,
    rust_2018_idioms,
    unreachable_pub,
    bad_style,
    const_err,
    dead_code,
    improper_ctypes,
    non_shorthand_field_patterns,
    no_mangle_generic_items,
    overflowing_literals,
    path_statements,
    patterns_in_fns_without_body,
    private_in_public,
    unconditional_recursion,
    unused,
    unused_allocation,
    unused_comparisons,
    unused_parens,
    while_true
)]
use std::error::Error;
use std::fmt::{self, Debug, Display};

struct Erased;

/// An Error bundled with a Context can then later be extracted from a chain of dyn Errors.
///
/// # Usage
///
/// This type has two primary methods of construction, `From` and [`Bundle`]. The first method of
/// construction, the `From` trait, only works when the type you're bundling with the error
/// implements `Default`. This is useful for types like `Backtrace`s where the context you care
/// about is implicitly captured just by constructing the type, or for types that have a reasonable
/// default like HttpStatusCodes defaulting to 500.
///
/// ```
/// use extracterr::Bundled;
///
/// #[derive(Debug, thiserror::Error)]
/// #[error("just an example error")]
/// struct ExampleError;
///
/// struct StatusCode(u32);
///
/// impl Default for StatusCode {
///     fn default() -> Self {
///         Self(500)
///     }
/// }
///
///
/// fn foo() -> Result<(), Bundled<ExampleError, StatusCode>> {
///     Err(ExampleError)?
/// }
/// ```
///
/// The second method of construction, the [`Bundle`] trait, lets you attach context to errors
/// manually. This is useful for types that don't implement `Default` or types where you only
/// occasionally want to override the defaults.
///
/// ```
/// use extracterr::{Bundled, Bundle};
///
/// #[derive(Debug, thiserror::Error)]
/// #[error("just an example error")]
/// struct ExampleError;
///
/// struct StatusCode(u32);
///
/// fn foo() -> Result<(), Bundled<ExampleError, StatusCode>> {
///     Err(ExampleError).bundle(StatusCode(404))?
/// }
/// ```
///
/// Once context has been bundled with an error it can then be extracted by an error reporter with
/// the [`Extract`] trait.
///
/// [`Bundle`]: trait.Bundle.html
/// [`Bundled`]: struct.Bundled.html
/// [`Extract`]: trait.Extract.html
pub struct Bundled<E, C: 'static> {
    inner: ErrorImpl<E, C>,
}

impl<E, C: 'static> Bundled<E, C> {
    fn bundle(error: E, context: C) -> Bundled<E, C>
    where
        E: Error + Send + Sync + 'static,
    {
        // # SAFETY
        //
        // This function + the repr(C) on the ErrorImpl make the type erasure throughout the rest
        // of this struct's methods safe. This saves a function pointer that is parameterized on the Error type
        // being stored inside the ErrorImpl. This lets the object_ref function safely cast a type
        // erased `ErrorImpl` back to its original type, which is needed in order to forward our
        // error/display/debug impls to the internal error type from the type erased error type.
        //
        // The repr(C) is necessary to ensure that the struct is layed out in the order we
        // specified it so that we can safely access the vtable and spantrace fields thru a type
        // erased pointer to the original object.
        let vtable = &ErrorVTable {
            object_ref: object_ref::<E, C>,
        };

        Self {
            inner: ErrorImpl {
                vtable,
                context,
                error,
            },
        }
    }

    /// Returns a reference to the inner error
    pub fn inner(&self) -> &E {
        &self.inner.error
    }
}

impl<E, C> From<E> for Bundled<E, C>
where
    E: Error + Send + Sync + 'static,
    C: Default,
{
    fn from(error: E) -> Self {
        Self::bundle(error, C::default())
    }
}

#[repr(C)]
struct ErrorImpl<E, C: 'static> {
    vtable: &'static ErrorVTable<C>,
    context: C,
    // NOTE: Don't use directly. Use only through vtable. Erased type may have
    // different alignment.
    error: E,
}

impl<C> ErrorImpl<Erased, C> {
    pub(crate) fn error(&self) -> &(dyn Error + Send + Sync + 'static) {
        // # SAFETY
        //
        // this function is used to cast a type-erased pointer to a pointer to error's
        // original type. the `ErrorImpl::error` method, which calls this function, requires that
        // the type this function casts to be the original erased type of the error; failure to
        // uphold this is UB. since the `From` impl is parameterized over the original error type,
        // the function pointer we construct here will also retain the original type. therefore,
        // when this is consumed by the `error` method, it will be safe to call.
        unsafe { &*(self.vtable.object_ref)(self) }
    }
}

struct ErrorVTable<C: 'static> {
    object_ref: unsafe fn(&ErrorImpl<Erased, C>) -> &(dyn Error + Send + Sync + 'static),
}

// # SAFETY
//
// This function must be parameterized on the type E of the original error that is being stored
// inside of the `ErrorImpl`. When it is parameterized by the correct type, it safely
// casts the erased `ErrorImpl` pointer type back to the original pointer type.
unsafe fn object_ref<E, C>(e: &ErrorImpl<Erased, C>) -> &(dyn Error + Send + Sync + 'static)
where
    E: Error + Send + Sync + 'static,
{
    // Attach E's native Error vtable onto a pointer to e.error.
    &(*(e as *const ErrorImpl<Erased, C> as *const ErrorImpl<E, C>)).error
}

impl<E, C> Error for Bundled<E, C>
where
    E: std::error::Error + 'static,
{
    // # SAFETY
    //
    // This function is safe so long as all functions on `ErrorImpl<Erased>` uphold the invariant
    // that the wrapped error is only ever accessed by the `error` method. This method uses the
    // function in the vtable to safely convert the pointer type back to the original type, and
    // then returns the reference to the erased error.
    //
    // This function is necessary for the `downcast_ref` in `ExtractSpanTrace` to work, because it
    // needs a concrete type to downcast to and we cannot downcast to ErrorImpls parameterized on
    // errors defined in other crates. By erasing the type here we can always cast back to the
    // Erased version of the ErrorImpl pointer, and still access the internal error type safely
    // through the vtable.
    fn source<'a>(&'a self) -> Option<&'a (dyn Error + 'static)> {
        let erased =
            unsafe { &*(&self.inner as *const ErrorImpl<E, C> as *const ErrorImpl<Erased, C>) };
        Some(erased)
    }
}

impl<E, C> Debug for Bundled<E, C>
where
    E: std::error::Error,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.inner.error, f)
    }
}

impl<E, C> Display for Bundled<E, C>
where
    E: std::error::Error,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.inner.error, f)
    }
}

impl<C> Error for ErrorImpl<Erased, C> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.error().source()
    }
}

impl<C> Debug for ErrorImpl<Erased, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(std::any::type_name::<C>(), f)
    }
}

impl<C> Display for ErrorImpl<Erased, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(std::any::type_name::<C>(), f)
    }
}

/// Extension trait for bundling context with errors through `Result` types
pub trait Bundle<T, C> {
    /// The output error type after bundling with the provided context
    type Bundled;

    /// ```
    /// use extracterr::{Bundle, Bundled};
    ///
    /// struct Dummy(i32);
    ///
    /// fn do_thing() -> Result<(), std::io::Error> {
    ///     // ...
    ///     # Ok(())
    /// }
    ///
    /// let r = do_thing().bundle(Dummy(0)); //: Result<(), Bundled<std::io::Error, Dummy>>
    /// ```
    fn bundle(self, context: C) -> Result<T, Self::Bundled>;
}

impl<T, E, C> Bundle<T, C> for Result<T, E>
where
    E: Error + Send + Sync + 'static,
    C: 'static,
{
    type Bundled = Bundled<E, C>;

    fn bundle(self, context: C) -> Result<T, Self::Bundled> {
        self.map_err(|error| Bundled::bundle(error, context))
    }
}

/// Extension trait for extracting references to bundled context from `dyn Error` trait objects
pub trait Extract {
    /// # Example
    ///
    /// ```rust
    /// use std::error::Error;
    /// use backtrace::Backtrace;
    /// use extracterr::{Bundled, Extract};
    ///
    /// fn report(error: &(dyn Error + 'static)) {
    ///     let mut source = Some(error);
    ///     let mut ind = 0;
    ///     let mut backtrace = None;
    ///
    ///     while let Some(error) = source {
    ///         source = error.source();
    ///
    ///         if let Some(bt) = error.extract::<Backtrace>() {
    ///             backtrace = Some(bt);
    ///         } else {
    ///             println!("{}: {}", ind, error);
    ///             ind += 1;
    ///         }
    ///     }
    ///
    ///     if let Some(backtrace) = backtrace {
    ///         println!("\nBacktrace:\n{:?}", backtrace)
    ///     }
    /// }
    /// ```
    fn extract<C>(&self) -> Option<&C>
    where
        C: 'static;
}

impl Extract for dyn Error + 'static {
    fn extract<C>(&self) -> Option<&C>
    where
        C: 'static,
    {
        self.downcast_ref::<ErrorImpl<Erased, C>>()
            .map(|inner| &inner.context)
    }
}

impl Extract for dyn Error + Send + Sync + 'static {
    fn extract<C>(&self) -> Option<&C>
    where
        C: 'static,
    {
        self.downcast_ref::<ErrorImpl<Erased, C>>()
            .map(|inner| &inner.context)
    }
}
