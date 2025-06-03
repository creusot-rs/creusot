use rustc_middle::ty::TyCtxt;
use rustc_span::{DUMMY_SP, ErrorGuaranteed, Span};

pub type CreusotResult<T> = Result<T, Error>;

pub(crate) enum Error {
    MustPrint(Message),
    TypeCheck(CannotFetchThir),
}

// TODO: make this a vector of spans and strings
#[derive(Debug)]
pub struct Message {
    span: Span,
    msg: String,
}

impl Message {
    pub(crate) fn new(span: Span, msg: impl Into<String>) -> Self {
        Self { span, msg: msg.into() }
    }

    pub(crate) fn emit(self, tcx: TyCtxt) -> ! {
        // TODO: try to add a code back in
        tcx.dcx().span_fatal(self.span, self.msg)
    }
}

impl Error {
    pub(crate) fn msg(span: Span, msg: impl Into<String>) -> Self {
        Self::MustPrint(Message { span, msg: msg.into() })
    }
}

impl From<Message> for Error {
    fn from(value: Message) -> Self {
        Self::MustPrint(value)
    }
}
impl From<CannotFetchThir> for Error {
    fn from(value: CannotFetchThir) -> Self {
        Self::TypeCheck(value)
    }
}

/// This error should be raised when fetching a function's THIR failed, because of a
/// typechecking error.
///
/// In this case, you can call `.into()` on the raised [`ErrorGuaranteed`].
///
/// The error should usually be bubbled up to the caller, which should then proceed to
/// call [`Self::abort`].
///
/// Not doing this will cause a crash when the error is dropped.
#[derive(Debug)]
pub(crate) struct CannotFetchThir(());

impl From<ErrorGuaranteed> for CannotFetchThir {
    fn from(_: ErrorGuaranteed) -> Self {
        Self(())
    }
}

impl CannotFetchThir {
    /// Abort the program.
    pub(crate) fn abort(self, tcx: TyCtxt) {
        std::mem::forget(self);
        // Some of those errors may not show up until after `before_analysis` terminates
        tcx.dcx().abort_if_errors();
        // TODO: ideally this point should be unreachable: investigate why it isn't.
    }

    /// Merge two errors together, so that more errors may be reported.
    pub(crate) fn merge(&mut self, other: Self) {
        std::mem::forget(other)
    }

    pub(crate) fn merge_opt(opt: &mut Option<Self>, other: Self) {
        match opt {
            None => *opt = Some(other),
            Some(err) => err.merge(other),
        }
    }
}

impl Drop for CannotFetchThir {
    fn drop(&mut self) {
        panic!("internal error: all thir error should be handled");
    }
}

#[derive(Debug, Clone)]
pub struct InternalError(pub &'static str);

impl From<InternalError> for Error {
    fn from(err: InternalError) -> Error {
        Error::MustPrint(Message::new(DUMMY_SP, format!("internal error: {}", err.0)))
    }
}

impl std::fmt::Display for InternalError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "encountered errors during translation: '{}'", self.0)
    }
}
impl std::error::Error for InternalError {}
