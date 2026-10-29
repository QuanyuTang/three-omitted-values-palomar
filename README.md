# Three omitted values and non-Blaschke point divisors

**Authors: Quanyu Tang, Bokai Cui, Wei He, Tao Hu, Yanyang Li, Ke Wang, Zijun Yu.**

[![Lean and kernel verification](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/workflows/verify.yml/badge.svg?branch=main)](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/workflows/verify.yml?query=branch%3Amain)
[![Palomar full mechanical preflight](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/workflows/palomar-preflight.yml/badge.svg?branch=main)](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/workflows/palomar-preflight.yml?query=branch%3Amain)

This repository formalizes Theorem 1.2 of [Three omitted values and
non-Blaschke point divisors in half-planes](https://arxiv.org/abs/2608.26062v2).
Codex produced the Lean formalization from the paper's original informal
proof and an auxiliary exposition of that proof.

The theorem constructs a real meromorphic function on the complex plane whose
zero, one, and pole fibres are all infinite and lie on the real axis. For
every other value, the point divisor in each open half-plane fails the
Blaschke condition, with multiplicities counted. The function is not of
bounded type in either half-plane. The theorem is unconditional.

**Verified proof snapshot:**
[`1a6a4e27d5d6589a061dae64c44391e993cad5f8`](https://github.com/QuanyuTang/three-omitted-values-palomar/tree/1a6a4e27d5d6589a061dae64c44391e993cad5f8)
passed both the [repository checks](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/runs/40799377846)
and the [official full Palomar mechanical preflight](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/runs/40811878877).
The [recorded mechanical report](verification/mechanical-report-20261028.json)
has `status: pass`, with Lean, NanoDa, and con-ron accepting the proof and no
errors or warnings. Later workflow and documentation commits do not change
that fixed proof snapshot. Badges show the latest workflow results; submit
the exact checked commit. Mechanical preflight is separate from Palomar
submission, editorial review, and registration.

## Statement and proof

[`Challenge.lean`](Challenge.lean) states the theorem and defines its terms;
[`Solution.lean`](Solution.lean) connects the identical statement to the
completed proof in [`Theorem12Proof/`](Theorem12Proof/).
[`comparator.json`](comparator.json) compares the theorem and its transitive
statement definitions and permits only the three standard Lean axioms.

Mathlib represents a meromorphic function in normal form by a complex-valued
function that takes the default value zero at a pole. Consequently the finite
value fibres require analyticity at the point, while the pole fibre consists
of non-analytic points. Multiplicity is the positive part of the meromorphic
divisor of `F - a`. Summability is over the complex plane with terms outside
the relevant half-plane equal to zero. Since the only excluded points on the
Riemann sphere are `0`, `1`, and `∞`, every remaining value is represented by
a complex number `a ≠ 0, 1`.

The proof constructs a controlled Farey boundary and a normalized conformal
map, obtains the global meromorphic function by reflection, and derives the
divergent point families from modular lambda orbits. It includes proofs of
the needed cusp continuation, the half-plane Blaschke zero criterion, and the
arithmetic divergence estimate.
[`PROOF_OVERVIEW.md`](PROOF_OVERVIEW.md) maps the source statement to the
Lean definitions and outlines the proof.

## Reproducing the checks

Install the version in [`lean-toolchain`](lean-toolchain), then run:

```sh
lake exe cache get
lake build
lake env lean verification/Audit.lean
python3 scripts/check-lean-sources.py
python3 scripts/check-proof-trust.py
```

On Linux with `bubblewrap`, run the Palomar-style statement and independent
kernel checks:

```sh
./scripts/verify-comparator.sh
```

The `sorry` in `Challenge.lean` is the deliberate statement placeholder;
the solution and its proof dependencies contain no `sorry`. See
[`formalization.yaml`](formalization.yaml) for scope, source, automation, and
review metadata and [`THIRD_PARTY.md`](THIRD_PARTY.md) for source attribution.

This repository is preparation for a later submission. Palomar requires
a public repository and a pushed immutable commit before its verification can
begin; the submission process is described at the
[Palomar submission page](https://palomar-registry.org/how-to-submit).
