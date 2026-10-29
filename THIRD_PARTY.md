# Third-party and prior-development credits

The project uses [Mathlib](https://github.com/leanprover-community/mathlib4),
with the exact dependency revisions recorded in `lake-manifest.json`.

The modular lambda and related complex-analysis source under
`Theorem12Proof/NoWanderingDomains/` is ported and adapted from
[will1491/no-wandering-domains](https://github.com/will1491/no-wandering-domains/tree/0a6497b0cc9ed39a6a705bf013449635894b56d0)
at commit `0a6497b0cc9ed39a6a705bf013449635894b56d0`, authored by Will (Ziang)
Li and distributed under Apache-2.0. Original source copyright notices are
retained. The upstream project reports AI assistance in its development and
requests citation of [arXiv:2609.16027](https://arxiv.org/abs/2609.16027),
by Ziang Li and Yusheng Luo.

The interior Riemann-mapping arguments and extracted inverse-map lemmas
include adaptations from Quanyu Tang and Zuoqin Wang's
[Dirichlet formalization](https://github.com/QuanyuTang/polya-dirichlet-simply-connected-formalization-Palomar-version/tree/b70cda58ddc4f4761a5a857b056310e713412386)
at commit `b70cda58ddc4f4761a5a857b056310e713412386` (Apache-2.0), which
records Aristotle and Codex assistance.

Boundary and Jordan-curve components also include extracted or adapted code
from the authors' Apache-2.0 Neumann development snapshot at commit
`b37a190b8afc6efb128f204176d26deec8d88a8c`. That snapshot is included through
the checked-in source files; it is not a remote build dependency. Attribution
is retained in the corresponding source headers. Copies of the upstream
Apache-2.0 licence texts are in [`licenses/`](licenses/).

The source-requirement scanner, metadata validator, and Comparator wrapper in
`scripts/` are taken from the Apache-2.0
[Palomar starter template](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406).

The mathematical result formalized here is from the paper linked in the
README. Its original proof and manuscript separately disclose their own use
of AI.
