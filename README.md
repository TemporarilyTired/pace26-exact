# Submission to PACE26 Challenge

A repository containing two separate algorithms (agreement forest depth first search (AF-DFS) and hitting pair depth bounded search (HP-DBS)) and a combination of the two. These algorithms solve find the maximum agreement forest on rooted binary phylogenetic trees as defined in https://pacechallenge.org/2026/maf/.

This repository is a submission to PACE 26 (See https://pacechallenge.org/2026/ where eventually more (better) algorithms by other contestants will be posted). This repository contains three algorithms; HP-DBS should generally be the one to solve the most problem within one second, although AF-DFS can solve a few instances (the ones with a very large MAF) in a few seconds that HP-DBS can never solve. Therefore the combination (combined_solver) should be the one to solve the most instances; for this reason the binary `combined_solver` is the actual submission.

## Installation

The solver has been tested on Debian 13.5. The following assumes Debian 13.5, but should be easily translate to any operating system.

### Build prerequisites

To build the solver the following packages are required:

- `curl` (to install Rust)
- `build-essential` (C compiler and linker required by the rust toolchain)

You can install them on Debian with:

```bash
apt-get install -y \
  curl \
  build-essential
```

### Install Rust

You need an installation of Rust; to install the stable toolchain, run:

```bash
curl https://sh.rustup.rs -sSf | sh -s -- -y
source ~/.cargo/env
```

### Build

To build the submission binary:

```bash
cargo build --release --locked --bin combined_solver
```

## Compiler flags / features

The features do NOT need to be enabled in normal circumstances:

- `assert_validity`: flag is only meant for debugging purposes to enable code that performs checks on the data structures to, e.g., determine the origin of an incorrect state in the algorithm. This feature severely affects the performance.
- `logging`: this flag is meant to track performance data during runtime. The resulting output is not meant to be fully human-readable and can at times lead to huge amount of output.
