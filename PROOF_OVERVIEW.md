# Statement correspondence and proof outline

The compared statement in `Challenge.lean` is Theorem 1.2 of
[arXiv:2608.26062v2](https://arxiv.org/abs/2608.26062v2), with the following
representations.

| Mathematical notion | Lean formulation |
| --- | --- |
| Meromorphic on the plane | `MeromorphicNFOn F Set.univ` |
| Real meromorphic | `F (conj z) = conj (F z)` for every `z` |
| Finite `a`-point | `AnalyticAt ℂ F z ∧ F z = a` |
| Pole | `¬ AnalyticAt ℂ F z`, for a globally meromorphic normal form |
| Point multiplicity | Positive part of the meromorphic divisor of `F - a` |
| Half-plane Blaschke condition | Summability of `multiplicity * |im z| / (1 + ‖z‖²)` on that half-plane |
| Bounded type | A quotient of bounded analytic functions with nonzero denominator function |

Normal form chooses the value zero at a pole, so the analyticity condition in
the finite fibre is essential. The pole and finite fibres are disjoint. The
statement quantifies over all `a : ℂ` other than zero and one, exactly the
remaining values of the sphere after excluding `0`, `1`, and `∞`.

The main construction and its dependencies are organized as follows.

1. `SternBrocot`, `FareyCurves`, and the graph modules construct a continuous,
   locally finite chain of Farey arcs below a positive Gaussian-decaying graph.
   The Jordan-curve and boundary modules prove a normalized conformal map
   from the upper half-plane and its boundary correspondence.
2. The Gaussian comparison modules construct the comparison map and prove a
   quantitative estimate for the inverse conformal map. This supplies the
   weight comparison used in the later orbit calculation.
3. The modular lambda function takes real values on the open Farey arcs, so
   the composite reflects analytically across them. At a vertex, a quadratic
   bound for the horizontal displacement forces the inverse modular height to
   tend to infinity. A suitable one of `λ`, `1 - λ`, and `1 / λ` then tends to
   zero. Removing that normalized singularity gives a meromorphic germ; the
   germs assemble into the global normal-form function.
4. Even integers, odd integers, and even-integer translates of one half give
   infinitely many distinct boundary parameters for one-points, poles, and
   zero-points, respectively. These are proved to be genuine finite fibres or
   poles.
5. Every other value has a modular lambda lift. Explicit level-two modular
   orbits, shifted by even integers, yield injective point families with
   divergent Blaschke weight. The proof derives the needed totient divergence
   and the half-plane zero criterion rather than assuming them.
6. The point families imply divergence of the full multiplicity-weighted
   divisor. Real symmetry gives the lower-half-plane statement. The zero
   criterion excludes bounded type in the upper half-plane, and reflection
   excludes it in the lower half-plane.

`Theorem12Proof/Theorem12Research.lean` assembles these steps without
additional hypotheses. `Solution.lean` exports the compared declaration.
See `THIRD_PARTY.md` for the prior developments used in the proof.
