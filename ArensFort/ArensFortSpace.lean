import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic

/-!
# Arens–Fort space

This file defines the classical Arens–Fort space, a standard counterexample
in general topology, using the usual “eventually in column” definition.

The underlying set is `X := Option (ℕ × ℕ)` where `none` plays the role of
the special point `p`.

A set `s : Set X` is open if either:

* `none ∉ s`, or
* `none ∈ s` and only finitely many columns fail to eventually lie in `s`.

We prove this defines a topology.
-/

open Set

namespace Counterexample
namespace ArensFort

/-- The underlying type of the Arens–Fort space. -/
@[reducible]
def X := Option (ℕ × ℕ)

/-- A set `s` is eventually in column `m` if there exists `N` such that
all `(m,n)` with `n ≥ N` lie in `s`. -/
def eventually_in_column (s : Set X) (m : ℕ) : Prop :=
  ∃ N : ℕ, ∀ ⦃n⦄, n ≥ N → (some (m,n) : X) ∈ s

/-- The columns not eventually contained in `s`. -/
def bad_cols (s : Set X) : Set ℕ :=
  { m | ¬ eventually_in_column s m }

/-- Openness predicate defining the Arens–Fort topology. -/
def is_open_AF (s : Set X) : Prop :=
  none ∉ s ∨ (bad_cols s).Finite

/-- In `univ`, no column is bad. -/
lemma bad_cols_univ_empty :
    bad_cols (univ : Set X) = ∅ :=
by
  ext m
  simp [bad_cols, eventually_in_column]

/--
Topological space structure for the Arens–Fort space, defined by
`is_open_AF`.
-/
instance : TopologicalSpace X where
  IsOpen := is_open_AF

  isOpen_univ := by
    right
    simp [bad_cols_univ_empty]

  isOpen_inter :=
  by
    intro s t hs ht
    classical
    by_cases hns : none ∉ s
    · left; simp [hns]

    by_cases hnt : none ∉ t
    · left; simp [hnt]

    -- Both contain `none`, so they have finitely many bad columns.
    have fs : (bad_cols s).Finite := hs.resolve_left hns
    have ft : (bad_cols t).Finite := ht.resolve_left hnt

    -- We show: bad_cols(s ∩ t) ⊆ bad_cols s ∪ bad_cols t
    have hsubset :
        bad_cols (s ∩ t) ⊆ bad_cols s ∪ bad_cols t :=
    by
      intro m hm
      by_contra hcontra
      have hnot_s : m ∉ bad_cols s := by
        intro hmem; exact hcontra (Or.inl hmem)
      have hnot_t : m ∉ bad_cols t := by
        intro hmem; exact hcontra (Or.inr hmem)

      have hgood_s : eventually_in_column s m := by
        simpa [bad_cols] using hnot_s
      have hgood_t : eventually_in_column t m := by
        simpa [bad_cols] using hnot_t

      rcases hgood_s with ⟨Ns, hNs⟩
      rcases hgood_t with ⟨Nt, hNt⟩

      let N := max Ns Nt
      have hgood_inter : eventually_in_column (s ∩ t) m :=
        ⟨N, by
          intro n hn
          have hn_s : Ns ≤ n := (le_max_left _ _).trans hn
          have hn_t : Nt ≤ n := (le_max_right _ _).trans hn
          exact ⟨hNs hn_s, hNt hn_t⟩⟩

      -- contradiction: m ∈ bad_cols (s ∩ t)
      have h' := hm hgood_inter
      simp at h'

    right
    exact (fs.union ft).subset hsubset

  isOpen_sUnion :=
  by
    intro F hF
    classical
    by_cases hmem : none ∈ ⋃₀ F
    · rcases mem_sUnion.1 hmem with ⟨s, hsF, hns⟩
      have hs := hF s hsF
      have fs : (bad_cols s).Finite :=
        hs.resolve_left (by intro h; exact h hns)

      have hsubset :
          bad_cols (⋃₀ F) ⊆ bad_cols s :=
      by
        intro m hm
        by_contra hcontra
        have hgood : eventually_in_column s m := by
          simpa [bad_cols] using hcontra
        rcases hgood with ⟨N, hN⟩
        have hgood_union : eventually_in_column (⋃₀ F) m :=
          ⟨N, by
            intro n hn
            exact mem_sUnion.2 ⟨s, hsF, hN hn⟩⟩

        have h' := hm hgood_union
        simp at h'

      right
      exact fs.subset hsubset

    · left; simp [hmem]

/-- The Arens–Fort space is Hausdorff. -/
instance : T2Space X where
  t2 := fun x y hne => by
    rcases x with rfl | ⟨m, n⟩
    · rcases y with _ | ⟨m, n⟩
      · contradiction
      use {z | z ≠ some (m, n)}, {some (m, n)}
      constructor
      · right
        show (bad_cols {z | z ≠ some (m, n)}).Finite
        refine Set.Finite.subset (Set.finite_singleton m) fun m' hm' => by
          simp [bad_cols, Set.mem_singleton_iff] at hm' ⊢
          by_contra h
          simp [eventually_in_column, h] at hm'
      constructor
      · left; simp
      constructor
      · simp
      constructor
      · simp
      · simp [Set.disjoint_left]

    · rcases y with rfl | ⟨m', n'⟩
      · use {some (m, n)}, {z | z ≠ some (m, n)}
        constructor
        · left; simp
        constructor
        · right
          show (bad_cols {z | z ≠ some (m, n)}).Finite
          refine Set.Finite.subset (Set.finite_singleton m) fun m' hm' => by
            simp [bad_cols, Set.mem_singleton_iff] at hm' ⊢
            by_contra h
            simp [eventually_in_column, h] at hm'
        refine ⟨?_, ?_, ?_⟩
        · simp
        · simp
        · simp

      · by_cases h_eq : m = m'
        · subst h_eq
          have h_ne : n ≠ n' := by
            intro heq
            have : (m, n) = (m, n') := by simp [heq]
            have := congr_arg Option.some this
            exact hne this
          by_cases h : n < n'
          · -- Case: n < n'
            use {z | ∃ k, z = some (m, k) ∧ k < n'},
                {z | ∃ k, z = some (m, k) ∧ k ≥ n'}
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · left; simp
            · left; simp
            · use n
            · use n'
            · simp only [Set.disjoint_left]
              intro z ⟨k, hk_eq, hk_lt⟩ ⟨k', hk'_eq, hk'_ge⟩
              rw [hk_eq] at hk'_eq
              have : k = k' := by simp at hk'_eq; exact hk'_eq
              omega
          · -- Case: n' ≤ n
            push_neg at h
            use {z | ∃ k, z = some (m, k) ∧ n ≤ k},
                {z | ∃ k, z = some (m, k) ∧ k < n}
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · left; simp
            · left; simp
            · use n
            · use n'
              simp; omega
            · simp only [Set.disjoint_left]
              intro z ⟨k, hk_eq, hk_ge⟩ ⟨k', hk'_eq, hk'_lt⟩
              rw [hk_eq] at hk'_eq
              have : k = k' := by simp at hk'_eq; exact hk'_eq
              omega

        · use {z | ∃ k, z = some (m, k)}, {z | ∃ k, z = some (m', k)}
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · left; simp
          · left; simp
          · use n
          · use n'
          · simp only [Set.disjoint_left]
            intro z ⟨k, hkeq⟩ ⟨k', heq⟩
            rw [hkeq] at heq
            have : m = m' := by simp at heq; exact heq.1
            exact h_eq this

end ArensFort
end Counterexample
