//! Rejections
//!
//! Part of the power of the [`Filter`](../trait.Filter.html) system is being able to
//! reject a request from a filter chain. This allows for filters to be
//! combined with `or`, so that if one side of the chain finds that a request
//! doesn't fulfill its requirements, the other side can try to process
//! the request.
//!
//! Many of the built-in [`filters`](../filters) will automatically reject
//! the request with an appropriate rejection. However, you can also build
//! new custom [`Filter`](../trait.Filter.html)s and still want other routes to be
//! matchable in the case a predicate doesn't hold.
//!
//! # Example
//!
//! ```
//! use warp::Filter;
//!
//! // Filter on `/:id`, but reject with 400 if the `id` is `0`.
//! let route = warp::path::param()
//!     .and_then(|id: u32| {
//!         if id == 0 {
//!             Err(warp::reject::bad_request())
//!         } else {
//!             Ok("something since id is valid")
//!         }
//!     });
//! ```

use std::error::Error as StdError;
use std::fmt;

use http::{self, StatusCode};
use serde;
use serde_json;

use ::never::Never;

pub(crate) use self::sealed::{CombineRejection, Reject};

/// Error cause for a rejection.
pub type Cause = Box<StdError + Send + Sync>;

#[doc(hidden)]
#[deprecated(note = "this will be changed to return a NotFound rejection, use warp::reject::bad_request() to keep the old behavior")]
#[inline]
pub fn reject() -> Rejection {
    bad_request()
}

/// Rejects a request with `400 Bad Request`.
#[inline]
pub fn bad_request() -> Rejection {
    Rejection::other(Status(StatusCode::BAD_REQUEST))
}

/// Rejects a request with `403 Forbidden`
#[inline]
pub fn forbidden() -> Rejection {
    Rejection::other(Status(StatusCode::FORBIDDEN))
}

/// Rejects a request with `404 Not Found`.
#[inline]
pub fn not_found() -> Rejection {
    Rejection {
        reason: Reason::NotFound,
    }
}

// 405 Method Not Allowed
#[inline]
pub(crate) fn method_not_allowed() -> Rejection {
    Rejection::other(Status(StatusCode::METHOD_NOT_ALLOWED))
}

// 411 Length Required
#[inline]
pub(crate) fn length_required() -> Rejection {
    Rejection::other(Status(StatusCode::LENGTH_REQUIRED))
}

// 413 Payload Too Large
#[inline]
pub(crate) fn payload_too_large() -> Rejection {
    Rejection::other(Status(StatusCode::PAYLOAD_TOO_LARGE))
}

// 415 Unsupported Media Type
//
// Used by the body filters if the request payload content-type doesn't match
// what can be deserialized.
#[inline]
pub(crate) fn unsupported_media_type() -> Rejection {
    Rejection::other(Status(StatusCode::UNSUPPORTED_MEDIA_TYPE))
}

/// Rejects a request with `500 Internal Server Error`.
#[inline]
pub fn server_error() -> Rejection {
    Rejection::other(Status(StatusCode::INTERNAL_SERVER_ERROR))
}


/// Rejects a request with a specific status code.
#[inline]
pub fn status(status: StatusCode) -> Rejection {
    if status == StatusCode::NOT_FOUND {
        not_found()
    } else {
        Rejection::other(Status(status))
    }
}

/// Rejection of a request by a [`Filter`](::Filter).
pub struct Rejection {
    reason: Reason,
}

enum Reason {
    NotFound,
    Other(Box<self::sealed::BoxedReject>),
}

impl Rejection {
    fn other<E: Reject + Send + Sync + 'static>(other: E) -> Self {
        Rejection {
            reason: Reason::Other(Box::new(other)),
        }
    }

    /// Return the HTTP status code that this rejection represents.
    pub fn status(&self) -> StatusCode {
        Reject::status(self)
    }

    /// Add given `err` into `Rejection`.
    pub fn with<E>(self, err: E) -> Self
    where
        E: Into<Cause>,
    {
        let cause = err.into();

        Self {
            reason: Reason::Other(Box::new(With(self, cause)))
        }
    }

    /// Returns a json response for this rejection.
    pub fn json(&self) -> ::reply::Response {
        use http::header::{CONTENT_TYPE, HeaderValue};
        use hyper::Body;

        let code = self.status();
        let mut res = http::Response::default();
        *res.status_mut() = code;

        res.headers_mut().insert(CONTENT_TYPE, HeaderValue::from_static("application/json"));

        *res.body_mut() = match serde_json::to_string(&self) {
            Ok(body) => Body::from(body),
            Err(_) => Body::from("{}"),
        };

        res
    }

    /// Returns an error cause.
    pub fn cause(&self) -> Option<&Cause> {
        if let Reason::Other(ref err) = self.reason {
            return err.cause()
        }
        None
    }

    #[doc(hidden)]
    #[deprecated(note = "into_cause can no longer be provided")]
    pub fn into_cause<T>(self) -> Result<Box<T>, Self>
    where
        T: StdError + Send + Sync + 'static
    {
        Err(self)
    }
}

impl From<Never> for Rejection {
    #[inline]
    fn from(never: Never) -> Rejection {
        match never {}
    }
}

impl Reject for Never {
    fn status(&self) -> StatusCode {
        match *self {}
    }

    fn into_response(self) -> ::reply::Response {
        match self {}
    }

    fn cause(&self) -> Option<&Cause> {
        None
    }
}

impl Reject for Rejection {
    fn status(&self) -> StatusCode {
        match self.reason {
            Reason::NotFound => StatusCode::NOT_FOUND,
            Reason::Other(ref other) => other.status(),
        }
    }

    fn into_response(self) -> ::reply::Response {
        match self.reason {
            Reason::NotFound => {
                let mut res = http::Response::default();
                *res.status_mut() = StatusCode::NOT_FOUND;
                res
            },
            Reason::Other(other) => other.into_response(),
        }
    }

    #[inline]
    fn cause(&self) -> Option<&Cause> {
        Rejection::cause(&self)
    }
}

impl fmt::Debug for Rejection {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("Rejection")
            .field(&self.reason)
            .finish()
    }
}

impl fmt::Debug for Reason {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Reason::NotFound => f.write_str("NotFound"),
            Reason::Other(ref other) => fmt::Debug::fmt(other, f),

        }
    }
}

#[derive(Debug)]
struct Status(StatusCode);

impl Reject for Status {
    fn status(&self) -> StatusCode {
        self.0
    }

    fn into_response(self) -> ::reply::Response {
        use ::reply::ReplySealed;
        self.0.into_response()
    }

    fn cause(&self) -> Option<&Cause> {
        None
    }
}

#[derive(Debug)]
struct With<R: Reject>(R, Cause);

impl<R: Reject> Reject for With<R> {
    fn status(&self) -> StatusCode {
        self.0.status()
    }

    fn into_response(self) -> ::reply::Response {
        use http::header::{CONTENT_TYPE, HeaderValue};
        use hyper::Body;

        let mut res = self.0.into_response();

        let bytes = self.1.to_string();
        res.headers_mut().insert(CONTENT_TYPE, HeaderValue::from_static("text/plain"));
        *res.body_mut() = Body::from(bytes);

        res
    }

    fn cause(&self) -> Option<&Cause> {
        Some(&self.1)
    }
}

impl serde::Serialize for Rejection {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer
    {
        use serde::ser::SerializeMap;

        let mut map = serializer.serialize_map(None)?;
        let err = match self.cause() {
            Some(err) => err,
            None => return map.end()
        };

        map.serialize_key("description").and_then(|_| map.serialize_value(err.description()))?;
        map.serialize_key("message").and_then(|_| map.serialize_value(&err.to_string()))?;
        map.end()
    }
}

mod sealed {
    use http::StatusCode;
    use ::never::Never;
    use super::{Cause, Reason, Rejection};

    pub trait Reject: ::std::fmt::Debug + Send + Sync {
        fn status(&self) -> StatusCode;
        fn into_response(self) -> ::reply::Response;
        fn cause(&self) -> Option<&Cause> { None }
    }

    pub(super) trait BoxedReject: ::std::fmt::Debug + Send + Sync {
        fn boxed_status(&self) -> StatusCode;
        fn boxed_response(self: Box<Self>) -> ::reply::Response;
        fn boxed_cause(&self) -> Option<&Cause>;
    }

    impl<T: Reject> BoxedReject for T {
        fn boxed_status(&self) -> StatusCode {
            self.status()
        }
        fn boxed_response(self: Box<Self>) -> ::reply::Response {
            self.into_response()
        }
        fn boxed_cause(&self) -> Option<&Cause> {
            self.cause()
        }
    }

    impl Reject for Box<BoxedReject> {
        fn status(&self) -> StatusCode {
            (**self).boxed_status()
        }
        fn into_response(self) -> ::reply::Response {
            self.boxed_response()
        }
        fn cause(&self) -> Option<&Cause> {
            (**self).boxed_cause()
        }
    }

    fn _assert_object_safe() {
        fn _assert(_: &Reject) {}
        fn is_reject<T: Reject>() {}
        is_reject::<Box<BoxedReject>>();
    }

    pub trait CombineRejection<E>: Send + Sized {
        type Rejection: Reject + From<Self> + From<E>;

        fn combine(self, other: E) -> Self::Rejection;
    }

    impl CombineRejection<Rejection> for Rejection {
        type Rejection = Rejection;

        fn combine(self, other: Rejection) -> Self::Rejection {
            let reason = match (self.reason, other.reason) {
                (Reason::Other(left), Reason::Other(right)) => {
                    Reason::Other(Box::new(Combined(left, right)))
                },
                (Reason::Other(other), Reason::NotFound) |
                (Reason::NotFound, Reason::Other(other)) => {
                    // ignore the NotFound
                    Reason::Other(other)
                },
                (Reason::NotFound, Reason::NotFound) => {
                    Reason::NotFound
                }
            };

            Rejection {
                reason,
            }
        }
    }

    impl CombineRejection<Never> for Rejection {
        type Rejection = Rejection;

        fn combine(self, other: Never) -> Self::Rejection {
            match other {}
        }
    }

    impl CombineRejection<Rejection> for Never {
        type Rejection = Rejection;

        fn combine(self, _: Rejection) -> Self::Rejection {
            match self {}
        }
    }

    impl CombineRejection<Never> for Never {
        type Rejection = Never;

        fn combine(self, _: Never) -> Self::Rejection {
            match self {}
        }
    }

    #[derive(Debug)]
    struct Combined<A, B>(A, B);

    impl<A: Reject, B: Reject> Combined<A, B> {
        fn prefer_a(&self) -> bool {
            // Compare status codes, with this priority:
            // - NOT_FOUND is lowest
            // - METHOD_NOT_ALLOWED is second
            // - if one status code is greater than the other
            // - otherwise, prefer A...
            match (self.0.status(), self.1.status()) {
                (_, StatusCode::NOT_FOUND) => true,
                (StatusCode::NOT_FOUND, _) => false,
                (_, StatusCode::METHOD_NOT_ALLOWED) => true,
                (StatusCode::METHOD_NOT_ALLOWED, _) => false,
                (a, b) if a < b => false,
                _ => true,
            }
        }
    }

    impl<A: Reject, B: Reject> Reject for Combined<A, B> {
        fn status(&self) -> StatusCode {
            if self.prefer_a() {
                self.0.status()
            } else {
                self.1.status()
            }
        }

        fn into_response(self) -> ::reply::Response {
            if self.prefer_a() {
                self.0.into_response()
            } else {
                self.1.into_response()
            }
        }

        fn cause(&self) -> Option<&Cause> {
            if self.prefer_a() {
                self.0.cause()
            } else {
                self.1.cause()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use http::header::{CONTENT_TYPE};

    use super::*;
    use http::StatusCode;

    #[test]
    fn rejection_status() {
        assert_eq!(bad_request().status(), StatusCode::BAD_REQUEST);
        assert_eq!(forbidden().status(), StatusCode::FORBIDDEN);
        assert_eq!(not_found().status(), StatusCode::NOT_FOUND);
        assert_eq!(method_not_allowed().status(), StatusCode::METHOD_NOT_ALLOWED);
        assert_eq!(length_required().status(), StatusCode::LENGTH_REQUIRED);
        assert_eq!(payload_too_large().status(), StatusCode::PAYLOAD_TOO_LARGE);
        assert_eq!(unsupported_media_type().status(), StatusCode::UNSUPPORTED_MEDIA_TYPE);
        assert_eq!(server_error().status(), StatusCode::INTERNAL_SERVER_ERROR);
    }

    #[test]
    fn combine_rejections() {
        let left = bad_request().with("left");
        let right = server_error().with("right");
        let reject = left.combine(right);

        assert_eq!(reject.status(), StatusCode::INTERNAL_SERVER_ERROR);
        assert_eq!(reject.cause().unwrap().to_string(), "right");
    }

    #[test]
    fn combine_rejection_causes_with_some_left_and_none_server_error() {
        let left = bad_request().with("left");
        let right = server_error();
        let reject = left.combine(right);

        assert_eq!(reject.status(), StatusCode::INTERNAL_SERVER_ERROR);
        assert!(reject.cause().is_none());
    }

    #[test]
    fn combine_rejection_causes_with_some_left_and_none_right() {
        let left = bad_request().with("left");
        let right = bad_request();
        let reject = left.combine(right);

        assert_eq!(reject.status(), StatusCode::BAD_REQUEST);
        assert_eq!(reject.cause().unwrap().to_string(), "left");
    }

    #[test]
    fn combine_rejection_causes_with_none_left_and_some_right() {
        let left = bad_request();
        let right = server_error().with("right");
        let reject = left.combine(right);

        assert_eq!(reject.status(), StatusCode::INTERNAL_SERVER_ERROR);
        assert_eq!(reject.cause().unwrap().to_string(), "right");
    }

    #[test]
    fn into_response_with_none_cause() {
        let resp = bad_request().into_response();
        assert_eq!(400, resp.status());
        assert!(resp.headers().get(CONTENT_TYPE).is_none());
        assert_eq!("", response_body_string(resp))
    }

    #[test]
    fn into_response_with_some_cause() {
        let resp = server_error().with("boom").into_response();
        assert_eq!(500, resp.status());
        assert_eq!("text/plain", resp.headers().get(CONTENT_TYPE).unwrap());
        assert_eq!("boom", response_body_string(resp))
    }

    #[test]
    fn into_json_with_none_cause() {
        let resp = bad_request().json();
        assert_eq!(400, resp.status());
        assert_eq!("application/json", resp.headers().get(CONTENT_TYPE).unwrap());
        assert_eq!("{}", response_body_string(resp))
    }

    #[test]
    fn into_json_with_some_cause() {
        let resp = bad_request().with("boom").json();
        assert_eq!(400, resp.status());
        assert_eq!("application/json", resp.headers().get(CONTENT_TYPE).unwrap());
        let expected = "{\"description\":\"boom\",\"message\":\"boom\"}";
        assert_eq!(expected, response_body_string(resp))
    }

    fn response_body_string(resp: ::reply::Response) -> String {
        use futures::{Future, Stream, Async};

        let (_, body) = resp.into_parts();
        match body.concat2().poll() {
            Ok(Async::Ready(chunk)) => {
                String::from_utf8_lossy(&chunk).to_string()
            },
            err => unreachable!("{:?}", err)
        }
    }

    #[test]
    #[allow(deprecated)]
    fn into_cause() {
        use std::io;

        let reject = bad_request()
            .with(io::Error::new(io::ErrorKind::Other, "boom"));

        reject
            .into_cause::<io::Error>()
            .unwrap_err();
    }

    #[test]
    fn size_of_rejection() {
        assert_eq!(
            ::std::mem::size_of::<Rejection>(),
            ::std::mem::size_of::<(usize, usize)>(),
        );
    }
}
