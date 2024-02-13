[![Workflow Status](https://github.com/cigani/easy_retry/workflows/main/badge.svg)](https://github.com/cigani/easy_retry/actions?query=workflow%3A%22main%22)
[![Coverage Status](https://codecov.io/gh/cigani/easy_retry/branch/main/graph/badge.svg)](https://codecov.io/gh/cigani/easy_retry)

# easy_retry

## Easy Retry

`easy_retry` is a Rust library that provides utilities for retrying operations with different strategies.

This library provides several retry strategies, including linear, exponential, and their asynchronous versions. You can choose the strategy that best fits your needs.

The library is designed to be simple and easy to use. It provides a single enum, `EasyRetry`, that represents different retry strategies. You can create a new retry strategy by calling one of the `new_*` methods on the `EasyRetry` enum.

The library provides a `run` method that takes a closure and runs the operation with the specified retry strategy. The `run` method returns the result of the operation, or an error if the operation fails after all retries.

The run method expects the closure to return a `Result` type. The `Ok` variant should contain the result of the operation, and the `Err` variant should contain the error that occurred during the operation.

## Features

* **Linear Retry**: In this strategy, the delay between retries is constant.
* **Exponential Retry**: In this strategy, the delay between retries doubles after each retry.
* **Linear Async Retry**: This is an asynchronous version of the linear retry strategy. This feature is only available when the `async` feature is enabled.
* **Exponential Async Retry**: This is an asynchronous version of the exponential retry strategy. This feature is only available when the `async` feature is enabled.

## Examples

```rust
use easy_retry::EasyRetry;

fn my_sync_fn(_n: &str) -> Result<(), std::io::Error> {
    Err(std::io::Error::new(std::io::ErrorKind::Other, "generic error"))
}

// Retry the operation with a linear strategy (1 second delay, 2 retries)
let retry_strategy = EasyRetry::new_linear(1, 2);
let result = retry_strategy.run(|| my_sync_fn("Hi"));
assert!(result.is_err());

```

## Asynchronous Example

```rust
use easy_retry::EasyRetry;

async fn my_async_fn(_n: u64) -> Result<(), std::io::Error> {
   Err(std::io::Error::new(std::io::ErrorKind::Other, "generic error"))
}

#[tokio::main]
async fn main() {
    // Retry the operation with an exponential strategy (1 second delay, 2 retries)
    let retry_strategy = EasyRetry::new_exponential_async(1, 2);
    let result = retry_strategy.run_async(|| my_async_fn(42)).await;
    assert!(result.is_err());

}
```
## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
easy_retry = "0.1.0"
```

Then, add this to your crate root (`main.rs` or `lib.rs`):

```rust
extern crate easy_retry;
```

Now, you can use the `EasyRetry` enum to create a retry strategy:

```rust
use easy_retry::EasyRetry;

let retry_strategy = EasyRetry::new_linear(100, 5);
```

## License

This project is licensed under the MIT License.

License: MIT
