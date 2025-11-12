# Arens–Fort Space

A formalization of the **Arens–Fort space** in [Lean 4](https://lean-lang.org/) using [Mathlib](https://github.com/leanprover-community/mathlib4).

## Overview

The Arens–Fort space is a classical counterexample in topology. It's a Hausdorff and regular space that is **not normal**—making it a key example demonstrating the limits of separation axioms in general topology.

### Construction

The space is defined on `X := Option (ℕ × ℕ)` where:
- `none` represents a special distinguished point $p$
- `some (m, n)` represents points in the natural number grid

A set `s ⊆ X` is **open** if and only if:
1. `p ∉ s`, OR
2. `p ∈ s` and only finitely many columns are "bad"

A column $m$ is **bad** if it's not eventually contained in $s$—that is, there is no threshold $N$ such that all points `some (m, n)` with $n ≥ N$ belong to $s$.

## Contents

- `ArensFort/Basic.lean` - Definition of the Arens–Fort topology and proofs of the topological axioms

## Building

Requires [Lean 4](https://lean-lang.org/) and [Lake](https://github.com/leanprover/lake).

```bash
lake build
```

## References

- Arens, Richard F., and James Dugundji. "Topologies for function spaces." Pacific Journal of Mathematics 1.1 (1951): 5-31.
- Steen, Lynn A., and J. Arthur Seebach. Counterexamples in topology. Courier Corporation, 1995.
