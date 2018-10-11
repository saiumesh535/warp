#![deny(warnings)]

extern crate pretty_env_logger;
extern crate warp;

use std::error::Error as StdError;
use std::fmt::{self, Display};

use warp::{Filter, Rejection, Reply};
use warp::http::StatusCode;

#[derive(Debug)]
enum Error {
    Oops,
    NotFound
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.description())
    }
}

impl StdError for Error {
    fn description(&self) -> &str {
        match self {
            Error::Oops => ":fire: this is fine",
            Error::NotFound => "you get a 404, and *you* get a 404...",
        }
    }

    fn cause(&self) -> Option<&StdError> {
        None
    }
}


fn main() {
    let hello = warp::path::index()
        .map(warp::reply);

    let oops = warp::path("oops")
        .and_then(|| {
            Err::<StatusCode, _>(warp::reject::bad_request().with(Error::Oops))
        });

    let not_found = warp::path("not_found")
        .and_then(|| {
            Err::<StatusCode, _>(warp::reject::bad_request().with(Error::NotFound))
        });

    let routes = warp::get2()
        .and(hello.or(oops).or(not_found))
        .recover(customize_error);

    warp::serve(routes)
        .run(([127, 0, 0, 1], 3030));
}

// This function receives a `Rejection` and tries to return a custom
// value, othewise simply passes the rejection along.
//
// NOTE: We don't *need* to return an `impl Reply` here, it's just
// convenient in this specific case.
fn customize_error(err: Rejection) -> Result<impl Reply, Rejection> {

    let code = match err.cause().and_then(|cause| cause.downcast_ref::<Error>()) {
        Some(&Error::NotFound) => StatusCode::NOT_FOUND,
        Some(&Error::Oops) => StatusCode::INTERNAL_SERVER_ERROR,
        None => return Err(err)
    };

    let mut resp = err.json();
    *resp.status_mut() = code;
    Ok(resp)
}
