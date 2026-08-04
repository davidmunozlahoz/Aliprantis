# Aliprantis

Lean 4 formalization of five counterexamples about
Hausdorff locally solid vector lattices and their topological
completions, answering open questions of C. D. Aliprantis.

The project is built on [Mathlib](https://github.com/leanprover-community/mathlib4)
and [BanLat](https://github.com/davidmunozlahoz/banlat).

## Main results

Each question is developed in its own module. The links below go directly to
the final theorem in that module.

1. [Theorem 2.5 — `theorem2_5`](Aliprantis/Q1.lean#L1008): there exists a
   Hausdorff sigma-Lebesgue locally convex-solid vector lattice whose
   topological completion is not sigma-Lebesgue.

2. [Theorem 3.6 — `theorem3_6`](Aliprantis/Q2.lean#L1609): there exists a
   Hausdorff locally convex-solid vector lattice with property `(B, i)` whose
   topological completion does not have property `(B, i)`.

3. [Theorem 4.4 — `theorem4_4`](Aliprantis/Q3.lean#L732): there exists a
   Hausdorff locally convex-solid vector lattice whose completion contains a
   positive element that is not the limit of a decreasing sequence of upper
   elements.

4. [Theorem 5.4 — `theorem5_4`](Aliprantis/Q4.lean#L695): there exists a
   Hausdorff locally convex-solid vector lattice satisfying the generalized
   `(A, 0)` property whose canonical image in its completion is not regular.

5. [Theorem 6.3 — `theorem6_3`](Aliprantis/Q5.lean#L410): there exists a
   Hausdorff locally convex-solid vector lattice whose canonical image in its
   completion is regular but not order dense.

## Building

From the repository root, download the precompiled Mathlib artifacts and
build the project:

```bash
lake exe cache get
lake build
```

The root `Aliprantis` library imports all five question modules, so
`lake build` checks the entire formalization.