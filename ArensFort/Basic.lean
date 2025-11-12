import Mathlib.Topology.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic

/-!
Arens–Fort space

We define the Arens–Fort space on X := Option (ℕ × ℕ) where `none` is the special
point `p` and `some (m,n)` are the remaining points. A set `s` is open iff either
it does not contain `p`, or `p ∈ s` and for all but finitely many `m : ℕ` there
exists `N` such that for all `n ≥ N` we have `some (m,n) ∈ s`.
-/

namespace ArensFort

open Set

@[reducible]
def X := Option (ℕ × ℕ)

/- predicate: a column `m` is eventually contained in `s` -/
def eventually_in_column (s : Set X) (m : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (some (m, n) : X) ∈ s

/- the 'bad' columns for a set `s` are those that are not eventually contained -/
def bad_cols (s : Set X) : Set ℕ :=
  { m | ¬ eventually_in_column s m }

/-- The Arens–Fort openness predicate. -/
def is_open_AF (s : Set X) : Prop :=
  none ∉ s ∨ (Finite (bad_cols s))

/- Now build the topology. We must show the usual axioms. -/
instance : TopologicalSpace X where
  IsOpen := is_open_AF
  isOpen_univ :=
    by
    -- univ contains every point, so every column is eventually in `univ` (use N = 0)
    have eventually_univ : ∀ m, eventually_in_column (univ : Set X) m := by
      intro m
      use 0
      intro n hn
      simp
    have empty_bad : bad_cols (univ : Set X) = ∅ := by
      ext m
      simp [bad_cols, eventually_in_column]
    right
    rw [empty_bad]
    exact finite_empty

  isOpen_inter :=
    by
    intro s t hs ht
    by_cases hns : none ∉ s
    · -- none ∉ s, so none ∉ s ∩ t
      left
      simp [hns]
    by_cases hnt : none ∉ t
    · left
      simp [hnt]
    -- both s and t contain `none`; extract the finite bad_cols witnesses
    -- derive the `Finite (bad_cols ·)` from the `is_open_AF` disjunctions
    have f_s : Finite (bad_cols s) :=
      match hs with
      | Or.inl h => False.elim (hns h)
      | Or.inr h => h
    have f_t : Finite (bad_cols t) :=
      match ht with
      | Or.inl h => False.elim (hnt h)
      | Or.inr h => h
    -- show bad_cols (s ∩ t) ⊆ bad_cols s ∪ bad_cols t
    have subset_union : bad_cols (s ∩ t) ⊆ bad_cols s ∪ bad_cols t := by
      intro m hm
      by_contra hnot
      simp at hnot
      -- hnot : (m ∉ bad_cols s) ∧ (m ∉ bad_cols t)
      rcases hnot with ⟨hnot_s, hnot_t⟩
      -- convert `m ∉ bad_cols s` to `eventually_in_column s m` and extract Ns
      have hgood_s := by simpa [bad_cols, eventually_in_column] using hnot_s
      have hgood_t := by simpa [bad_cols, eventually_in_column] using hnot_t
      rcases hgood_s with ⟨Ns, hNs⟩
      rcases hgood_t with ⟨Nt, hNt⟩
      let N := max Ns Nt
      have : ∀ n, n ≥ N → (some (m, n) : X) ∈ s ∩ t := by
        intro n hn
        have Ns_le_n : Ns ≤ n := (le_max_left Ns Nt).trans hn
        have Nt_le_n : Nt ≤ n := (le_max_right Ns Nt).trans hn
        refine ⟨hNs n Ns_le_n, hNt n Nt_le_n⟩
      simpa [bad_cols, eventually_in_column] using hm ⟨N, this⟩
    -- union of finite sets is finite, so bad_cols (s ∩ t) is finite
    right
    have h1 : Set.Finite (bad_cols s) := by
      simpa [Set.finite_coe_iff] using f_s
    have h2 : Set.Finite (bad_cols t) := by
      simpa [Set.finite_coe_iff] using f_t
    exact Set.Finite.subset (h1.union h2) subset_union

  isOpen_sUnion :=
    by
    intro F hF
    by_cases hmem : none ∈ ⋃₀ F
    · -- none is in the union, pick a member set `s ∈ F` with `none ∈ s`
      rcases mem_sUnion.1 hmem with ⟨s, s_in, hns⟩
      -- s is open, so its bad_cols is finite; show bad_cols (⋃₀ F) ⊆ bad_cols s
      have key : bad_cols (⋃₀ F) ⊆ bad_cols s := by
        intro m hm
        -- if m were good for s then union would be good, so hm implies m is bad for s
        by_contra H
        have Hgood := by simpa [bad_cols, eventually_in_column] using H
        rcases Hgood with ⟨N, hN⟩
        -- then for all n ≥ N, some (m,n) ∈ s ⊆ ⋃₀ F, contradiction
        have : ∀ n, n ≥ N → (some (m, n) : X) ∈ ⋃₀ F := by
          intro n hn
          exact mem_sUnion.2 ⟨s, s_in, hN n hn⟩
        simpa [bad_cols, eventually_in_column] using hm ⟨N, this⟩
      -- extract the Finite (bad_cols s) from the fact `s` is open
      have hs_open := hF s s_in
      have hfs_s : Finite (bad_cols s) := match hs_open with
        | Or.inl h => False.elim (h hns)
        | Or.inr h => h
      right
      exact Finite.subset hfs_s key
    · -- none ∉ ⋃₀ F, so the union is open by the `none ∉` branch
      left
      exact hmem

end ArensFort
