//! This crate provides helpers for bundling context with errors and later
//! extracting said context thru `dyn Error` trait objects.
//!
//! ## Setup
//!
//! ```toml
//! [dependencies]
//! extracterr = "0.1"
//! ```
//!
//! ## Example
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
//! let error: Bundled<_, Backtrace> = error.into();
//! let error: Box<dyn Error + Send + Sync + 'static> = error.into();
//!
//! // first error in chain should be the error itself
//! assert_eq!("Example Error", error.to_string());
//! assert!(error.extract::<Backtrace>().is_none());
//!
//! let error = error.source().unwrap();
//! let backtrace = error.extract::<Backtrace>();
//!
//! assert!(backtrace.is_some());
//! // The Display / Debug impls of the fake error that contains the bundled context print the
//! // context's type_name
//! assert_eq!(error.to_string(), std::any::type_name::<Backtrace>());
//! ```
#![doc(html_root_url = "https://docs.rs/extracterr/0.1.0")]
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

///
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

///
pub trait Bundle<T, C> {
    ///
    type Bundled;

    /// ```
    /// use extracterr::{Bundle, Bundled};
    ///
    /// fn do_thing() -> Result<(), std::io::Error> {
    ///     // ...
    ///     # Ok(())
    /// }
    ///
    ///
    /// #[derive(Debug)]
    /// struct Dummy(i32);
    ///
    /// impl std::fmt::Display for Dummy {
    ///     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    ///         write!(f, "{}", self.0)
    ///     }
    /// }
    ///
    /// let r: Result<(), Bundled<std::io::Error, Dummy>> = do_thing().bundle(Dummy(0));
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

///
pub trait Extract {
    ///
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
