#[cfg(feature = "assert_validity")]
macro_rules! assert_validity {
    ($body:expr) => {
        $body.assert_validity();
    };
}

#[cfg(not(feature = "assert_validity"))]
macro_rules! assert_validity {
    ($body:expr) => {};
}

pub(crate) use assert_validity;
