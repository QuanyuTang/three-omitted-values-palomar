# Three omitted values and non-Blaschke point divisors

**Authors: Quanyu Tang, Bokai Cui, Wei He, Tao Hu, Yanyang Li, Ke Wang, Zijun Yu.**

[![Lean and kernel verification](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/workflows/verify.yml/badge.svg?branch=main)](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/workflows/verify.yml?query=branch%3Amain)
[![Palomar full mechanical preflight](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/workflows/palomar-preflight.yml/badge.svg?branch=main)](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/workflows/palomar-preflight.yml?query=branch%3Amain)

**Registered with Palomar:**
[PALOMAR-2026-10-29-000014, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-29-000014&version=1),
registered on October 29, 2026. The record fixes the source snapshot
[`c408da985b3b0498f6f2df702739673865a8b932`](https://github.com/QuanyuTang/three-omitted-values-palomar/tree/c408da985b3b0498f6f2df702739673865a8b932).

This repository formalizes Theorem 1.2 of [Three omitted values and
non-Blaschke point divisors in half-planes](https://arxiv.org/abs/2608.26062v2).
Codex produced the Lean formalization from the paper's original informal
proof and an auxiliary exposition of that proof.

The theorem constructs a real meromorphic function on the complex plane whose
zero, one, and pole fibres are all infinite and lie on the real axis. For
every other value, the point divisor in each open half-plane fails the
Blaschke condition, with multiplicities counted. The function is not of
bounded type in either half-plane. The theorem is unconditional.

**Verification of the registered snapshot:** The
[Palomar verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/40823219946)
passed for the registered commit. The same snapshot also passed the
[repository checks](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/runs/40818912274)
and the [full mechanical preflight](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/runs/40818923518).
Lean, NanoDa, and con-ron accepted the proof; the axiom audit of the main
theorem and all 15 semantic correspondence theorems passed.

**Earlier verification evidence:**
[`1a6a4e27d5d6589a061dae64c44391e993cad5f8`](https://github.com/QuanyuTang/three-omitted-values-palomar/tree/1a6a4e27d5d6589a061dae64c44391e993cad5f8)
passed both the [repository checks](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/runs/40799377846)
and the [official full Palomar mechanical preflight](https://github.com/QuanyuTang/three-omitted-values-palomar/actions/runs/40811878877).
The [recorded mechanical report](verification/mechanical-report-20261028.json)
has `status: pass`, with Lean, NanoDa, and con-ron accepting the proof. Its
top-level `errors` and `warnings` lists are empty; the Lean build logs
contain routine linter and deprecation warnings. This historical report
predates the explicit semantic correspondence module added in the current
sources. It is retained as historical evidence; the Palomar record above
identifies the registered version and its verification evidence.

## Statement and proof

[`Challenge.lean`](Challenge.lean) states the theorem and defines its terms;
[`Solution.lean`](Solution.lean) connects the identical statement to the
completed proof in [`Theorem12Proof/`](Theorem12Proof/).
[`comparator.json`](comparator.json) compares the theorem and its transitive
statement definitions and permits only the three standard Lean axioms.

**The single `sorry` in `Challenge.lean` is a deliberate statement placeholder.**
`Solution.lean` does not import `Challenge.lean`; the proved solution and its
dependencies contain no `sorry`. The metadata's zero placeholder count describes
the completed proof, excluding that statement-only placeholder.

Mathlib represents a meromorphic function in normal form by a complex-valued
function that takes the default value zero at a pole. Consequently the finite
value fibres require analyticity at the point, while the pole fibre consists
of non-analytic points. Multiplicity is the positive part of the meromorphic
divisor of `F - a`. Summability is over the complex plane with terms outside
the relevant half-plane equal to zero. Since the only excluded points on the
Riemann sphere are `0`, `1`, and `∞`, every remaining value is represented by
a complex number `a ≠ 0, 1`.

[`SemanticCorrespondence.lean`](Theorem12Proof/SemanticCorrespondence.lean)
proves the corresponding finite and infinite `OnePoint ℂ` fibre identities,
the equivalence of the remaining-value quantifiers, equality with analytic
zero multiplicities, and equivalence of the zero-padded and actual-fibre sums.
It also proves `bounded_type_upper_agrees` and `bounded_type_lower_agrees`:
on these pole-free half-planes the predicates agree with quotients of bounded
holomorphic functions. Holomorphy there follows from the theorem's existing
real-pole conclusion. `source_form_with_semantic_bridges` combines these facts
in an unconditional restatement. This is a representation and terminology
bridge, rather than a separate manifold formalization of the Riemann sphere.

CI compiles this module as a dependency of `Solution` and checks the permitted
axioms of every bridge theorem. The review remains self-assessed; external AI
feedback and kernel verification are not independent human expert review.

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
lake env lean verification/Audit.lean > axiom-audit.log
python3 scripts/check-axiom-audit.py axiom-audit.log
python3 scripts/check-lean-sources.py
python3 scripts/check-proof-trust.py
```

On Linux with `bubblewrap`, run the Palomar-style statement and independent
kernel checks:

```sh
./scripts/verify-comparator.sh
```

See
[`formalization.yaml`](formalization.yaml) for scope, source, automation, and
review metadata and [`THIRD_PARTY.md`](THIRD_PARTY.md) for source attribution.

The [Palomar version 1 record](https://palomar-registry.org/entry?id=PALOMAR-2026-10-29-000014&version=1)
refers to the fixed source snapshot linked above. Later documentation updates
on `main` do not change that registered snapshot.
