/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Compact convex hulls

## Main results

* `IsCompact.convexHull`: In a finite-dimensional real normed space, the convex hull of a compact
  set is compact.
-/

public section

open Set

universe u v

private theorem sum_extend_fin_aux {V : Type u} {M : Type v} [AddCommMonoid M] (t : Finset V)
    {n : ℕ} (hcard : t.card ≤ n) (f : V → M) :
    (∑ j : Fin n, if h : (j : ℕ) < t.card then f (t.equivFin.symm ⟨j, h⟩ : V) else 0) =
      ∑ y ∈ t, f y := by
  calc
    (∑ j : Fin n, if h : (j : ℕ) < t.card then f (t.equivFin.symm ⟨j, h⟩ : V) else 0) =
        ∑ m ∈ Finset.range n,
          (if h : m < t.card then f (t.equivFin.symm ⟨m, h⟩ : V) else 0) :=
      Fin.sum_univ_eq_sum_range
        (fun m : ℕ ↦ if h : m < t.card then f (t.equivFin.symm ⟨m, h⟩ : V) else 0) n
    _ = ∑ m ∈ Finset.range t.card,
          (if h : m < t.card then f (t.equivFin.symm ⟨m, h⟩ : V) else 0) :=
      (Finset.sum_subset (Finset.range_subset_range.2 hcard)
        (fun m _ hm ↦ dite_eq_right (by simpa using hm))).symm
    _ = ∑ i : Fin t.card,
          (if h : (i : ℕ) < t.card then f (t.equivFin.symm ⟨i, h⟩ : V) else 0) :=
      (Fin.sum_univ_eq_sum_range
        (fun m : ℕ ↦ if h : m < t.card then f (t.equivFin.symm ⟨m, h⟩ : V) else 0)
        t.card).symm
    _ = ∑ i : Fin t.card, f (t.equivFin.symm i : V) :=
      Finset.sum_congr rfl fun i _ ↦ dite_eq_left i.2
    _ = ∑ y ∈ t, f y := by
      rw [Equiv.sum_comp t.equivFin.symm fun y : t ↦ f (y : V)]
      exact Finset.sum_coe_sort t f

/-- In a finite-dimensional real normed space, the convex hull of a compact set is compact. -/
theorem IsCompact.convexHull {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hs : IsCompact s) :
    IsCompact (_root_.convexHull ℝ s) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  let n := Module.finrank ℝ V + 1
  let S := stdSimplex ℝ (Fin n) ×ˢ univ.pi fun _ : Fin n ↦ s
  let Φ := fun p : (Fin n → ℝ) × (Fin n → V) ↦ ∑ i, p.1 i • p.2 i
  have hS : IsCompact S := (isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi fun _ ↦ hs)
  have hΦ : Continuous Φ := by fun_prop
  suffices _root_.convexHull ℝ s = Φ '' S by simpa only [this] using hS.image hΦ
  refine Subset.antisymm ?_ ?_
  · intro x hx
    rw [convexHull_eq_union] at hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨t, hts, ht, hxt⟩ := hx
    have hcard : t.card ≤ n := by
      simpa only [Fintype.card_coe, n] using
        (AffineIndependent.card_le_finrank_succ ht).trans
          (Nat.add_le_add_right (Submodule.finrank_le (vectorSpan ℝ (range ((↑) : t → V)))) 1)
    rw [t.convexHull_eq] at hxt
    obtain ⟨w, hw₀, hw₁, hwx⟩ := hxt
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁] at hwx
    refine ⟨⟨fun j ↦ if h : (j : ℕ) < t.card then w (t.equivFin.symm ⟨j, h⟩ : V) else 0,
        fun j ↦ if h : (j : ℕ) < t.card then (t.equivFin.symm ⟨j, h⟩ : V) else x₀⟩,
      ⟨⟨fun j ↦ ?_, ?_⟩, fun j _ ↦ ?_⟩, ?_⟩
    · dsimp only
      split
      · exact hw₀ _ (Finset.coe_mem _)
      · exact le_rfl
    · simpa using (sum_extend_fin_aux t hcard w).trans hw₁
    · dsimp only
      split
      · exact hts (Finset.coe_mem _)
      · exact hx₀
    · refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans
        ((sum_extend_fin_aux t hcard fun y ↦ w y • y).trans hwx)
      split <;> simp_all
  · rintro _ ⟨⟨u, z⟩, ⟨hu, hz⟩, rfl⟩
    exact mem_convexHull_of_exists_fintype u z hu.1 hu.2 (fun i ↦ hz i (mem_univ i)) rfl
