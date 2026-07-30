/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# The field of Puiseux series

This file defines the field of Puiseux series over a field `K` as a subfield of the Hahn series
field `HahnSeries ℚ K`, namely the directed union of the images of the embeddings
`LaurentSeries.toHahn K n : K((t)) →+* HahnSeries ℚ K` sending `t` to `t ^ (1 / n)`.

## Main definitions

* `LaurentSeries.expand K m`: the expansion ring endomorphism of `K((t))` sending `t` to `t ^ m`.
* `LaurentSeries.toHahn K n`: the ring embedding `K((t)) →+* HahnSeries ℚ K`
  sending `t` to `t ^ (1 / n)`.
* `PuiseuxSeries.subfield K`: the Puiseux subfield `⨆ n, (toHahn K n).fieldRange` of
  `HahnSeries ℚ K`.
* `PuiseuxSeries K`: the type of Puiseux series over `K`, a field, equipped with an algebra
  structure over `LaurentSeries K` via `toHahn K 1`.

## Main results

* `PuiseuxSeries.mem_subfield_iff`: membership in the Puiseux subfield is membership in the range
  of some `toHahn K n`.
* `PuiseuxSeries.mem_subfield_iff_support`: the classical bounded-denominator characterization —
  a Hahn series is a Puiseux series iff its support lies in `(1 / n) • ℤ` for a single `n`.
* `PuiseuxSeries.exists_common_index`: finitely many Puiseux series lie in the range of a single
  `toHahn K N`.

## Tags

puiseux series, laurent series, hahn series
-/

@[expose] public section

noncomputable section

open HahnSeries Polynomial

namespace LaurentSeries

variable (K : Type*) [Field K]

/-- The expansion ring embedding `K((t)) →+* K((t))`, `t ↦ t ^ m`:
`embDomainRingHom` along the exponent map `k ↦ m * k` on `ℤ`. -/
def expand (m : ℕ+) : LaurentSeries K →+* LaurentSeries K :=
  HahnSeries.embDomainRingHom
    (⟨⟨fun k => (m : ℤ) * k, mul_zero _⟩, fun _ _ => mul_add _ _ _⟩ : ℤ →+ ℤ)
    (fun _ _ h => by
      exact mul_left_cancel₀ (by exact_mod_cast m.ne_zero) h)
    (fun _ _ => mul_le_mul_iff_right₀ (by exact_mod_cast m.pos))

/-- The embedding `K((t)) →+* HahnSeries ℚ K`, "`t ↦ t ^ (1 / n)`":
`embDomainRingHom` along the exponent map `k ↦ k / n : ℤ → ℚ`. -/
def toHahn (n : ℕ+) : LaurentSeries K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom
    (AddMonoidHom.mk' (fun k : ℤ => (k : ℚ) / (n : ℕ)) fun a b => by push_cast; ring)
    (fun a b h => by
      have h' : (a : ℚ) / (n : ℕ) = (b : ℚ) / (n : ℕ) := h
      have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
      field_simp at h'
      exact_mod_cast h')
    (fun a b => by
      simp only [AddMonoidHom.mk'_apply]
      rw [div_le_div_iff_of_pos_right (by exact_mod_cast n.pos : (0 : ℚ) < (n : ℕ))]
      exact Int.cast_le)

@[simp]
theorem toHahn_single (n : ℕ+) (k : ℤ) (a : K) :
    toHahn K n (HahnSeries.single k a) = HahnSeries.single ((k : ℚ) / (n : ℕ)) a :=
  HahnSeries.embDomain_single ..

/-- Compatibility of the embeddings: `toHahn K n = toHahn K (n * m) ∘ expand K m` — expanding
by `m` and then mapping `t ↦ t ^ (1 / (n * m))` is mapping `t ↦ t ^ (1 / n)`. -/
theorem toHahn_comp_expand (n m : ℕ+) :
    (toHahn K (n * m)).comp (expand K m) = toHahn K n :=
  RingHom.ext fun f => by
    simp only [RingHom.comp_apply, toHahn, expand, HahnSeries.embDomainRingHom_apply,
      HahnSeries.embDomain_embDomain]
    congr 1
    ext k
    simp only [RelEmbedding.trans_apply, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      AddMonoidHom.mk'_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    push_cast
    rw [mul_comm ((n : ℚ)) ((m : ℚ)), mul_div_mul_left _ _ (by exact_mod_cast m.ne_zero)]

/-- Range monotonicity: the range of `toHahn K n` is contained in the range of
`toHahn K (n * m)`, as subfields of `HahnSeries ℚ K`. -/
theorem fieldRange_toHahn_le (n m : ℕ+) :
    (toHahn K n).fieldRange ≤ (toHahn K (n * m)).fieldRange := by
  rintro x ⟨f, rfl⟩
  exact ⟨expand K m f, by rw [← RingHom.comp_apply, toHahn_comp_expand]⟩

/-- The family `n ↦ (toHahn K n).fieldRange` is directed: the ranges of `toHahn K a` and
`toHahn K b` both sit inside the range of `toHahn K (a * b)`. -/
theorem directed_fieldRange_toHahn :
    Directed (· ≤ ·) fun n : ℕ+ => (toHahn K n).fieldRange := by
  intro a b
  refine ⟨a * b, fieldRange_toHahn_le K a b, ?_⟩
  rw [mul_comm]
  exact fieldRange_toHahn_le K b a

end LaurentSeries

namespace PuiseuxSeries

open LaurentSeries

variable (K : Type*) [Field K]

/-- The Puiseux subfield `⨆ n, (toHahn K n).fieldRange` of `HahnSeries ℚ K` — the directed union
of the images of the embeddings `toHahn K n`, i.e. `⋃ n, K((t ^ (1 / n)))`. -/
def subfield : Subfield (HahnSeries ℚ K) :=
  ⨆ n : ℕ+, (toHahn K n).fieldRange

/-- Membership in the Puiseux subfield: `x ∈ subfield K` iff `x` is in the range of some
`toHahn K n` (the supremum of the directed family of subfields is their union). -/
theorem mem_subfield_iff {x : HahnSeries ℚ K} :
    x ∈ subfield K ↔ ∃ n : ℕ+, x ∈ (toHahn K n).fieldRange :=
  Subfield.mem_iSup_of_directed (directed_fieldRange_toHahn K)

/-- **Bounded-denominator characterization**: membership in the Puiseux subfield
is exactly the classical support condition — the support lies in `(1 / n) • ℤ` for a
single `n`. This certifies the directed-union definition against the textbook
description of Puiseux series. -/
theorem mem_subfield_iff_support {x : HahnSeries ℚ K} :
    x ∈ subfield K ↔
      ∃ n : ℕ+, ∀ q ∈ x.support, ∃ k : ℤ, q = (k : ℚ) / (n : ℚ) := by
  classical
  -- the two coefficient facts about `toHahn K n`, obtained by unfolding it as an `embDomain`
  have key : ∀ (n : ℕ+) (f : LaurentSeries K),
      (∀ k : ℤ, ((toHahn K n) f).coeff ((k : ℚ) / (n : ℚ)) = f.coeff k) ∧
        (∀ q : ℚ, (¬ ∃ k : ℤ, q = (k : ℚ) / (n : ℚ)) → ((toHahn K n) f).coeff q = 0) := by
    intro n f
    obtain ⟨E, hEapp, hE⟩ : ∃ E : ℤ ↪o ℚ, (∀ k : ℤ, E k = (k : ℚ) / (n : ℚ)) ∧
        (toHahn K n) f = HahnSeries.embDomain E f := by
      refine ⟨⟨⟨fun k => (k : ℚ) / (n : ℕ), fun a b h => ?_⟩, fun {a b} => ?_⟩,
        fun _ => rfl, ?_⟩
      · have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
        field_simp at h
        exact_mod_cast h
      · simp only [Function.Embedding.coeFn_mk]
        rw [div_le_div_iff_of_pos_right (by exact_mod_cast n.pos : (0 : ℚ) < (n : ℕ))]
        exact Int.cast_le
      · rfl
    refine ⟨fun k => by rw [hE, ← hEapp k, HahnSeries.embDomain_coeff], fun q hq => ?_⟩
    rw [hE]
    exact HahnSeries.embDomain_of_notMem_range fun ⟨k, hk⟩ => hq ⟨k, by rw [← hk, hEapp]⟩
  rw [mem_subfield_iff]
  constructor
  · rintro ⟨n, f, rfl⟩
    refine ⟨n, fun q hq => ?_⟩
    by_contra hcon
    exact hq ((key n f).2 q hcon)
  · rintro ⟨n, hn⟩
    have hn0 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast n.pos
    refine ⟨n, ?_⟩
    rcases Set.eq_empty_or_nonempty x.support with hs | hs
    · exact ⟨0, (map_zero _).trans (HahnSeries.support_eq_empty_iff.mp hs).symm⟩
    -- the minimum of the support gives an integer lower bound for the support of `f`
    set q₀ : ℚ := x.isWF_support.min hs
    have hbdd : ∀ k : ℤ, x.coeff ((k : ℚ) / (n : ℚ)) ≠ 0 → ⌈(n : ℚ) * q₀⌉ ≤ k := by
      intro k hk
      refine Int.ceil_le.mpr ?_
      rw [mul_comm]
      exact (le_div_iff₀ hn0).mp (x.isWF_support.min_le hs hk)
    refine ⟨⟨fun k => x.coeff ((k : ℚ) / (n : ℚ)), ?_⟩, ?_⟩
    · rw [Set.isPWO_iff_isWF]
      exact BddBelow.isWF ⟨⌈(n : ℚ) * q₀⌉, hbdd⟩
    · ext q
      by_cases hq : ∃ k : ℤ, q = (k : ℚ) / (n : ℚ)
      · obtain ⟨k, rfl⟩ := hq
        exact (key n _).1 k
      · rw [(key n _).2 q hq]
        by_contra hc
        exact hq (hn q (Ne.symm hc))

/-- Common index: a finite set of elements of the Puiseux subfield lies in the
range of a single `toHahn K N`. -/
theorem exists_common_index (s : Finset (HahnSeries ℚ K))
    (hs : ∀ x ∈ s, x ∈ subfield K) :
    ∃ N : ℕ+, ∀ x ∈ s, x ∈ (toHahn K N).fieldRange := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a s ha ih =>
      obtain ⟨N₀, hN₀⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
      obtain ⟨n, hn⟩ := (mem_subfield_iff K).mp (hs a (Finset.mem_insert_self a s))
      refine ⟨n * N₀, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact fieldRange_toHahn_le K n N₀ hn
      · exact (mul_comm n N₀ ▸ fieldRange_toHahn_le K N₀ n) (hN₀ x hx)

end PuiseuxSeries

/-- The type of Puiseux series over `K`: the carrier of the Puiseux subfield of
`HahnSeries ℚ K`. A field, by the generic subfield instances. -/
def PuiseuxSeries (K : Type*) [Field K] : Type _ :=
  ↥(PuiseuxSeries.subfield K)

namespace PuiseuxSeries

variable (K : Type*) [Field K]

instance : Field (PuiseuxSeries K) :=
  inferInstanceAs (Field ↥(subfield K))

/-- The `K((t))`-algebra structure on Puiseux series: `toHahn K 1` corestricted to the
Puiseux subfield. This fixes the embedding of `K((t))` into the Puiseux series. -/
instance algebraLaurentSeries : Algebra (LaurentSeries K) (PuiseuxSeries K) :=
  RingHom.toAlgebra <|
    ((LaurentSeries.toHahn K 1).codRestrict (subfield K).toSubring fun x =>
        SetLike.le_def.mp
          (le_iSup (fun n : ℕ+ => (LaurentSeries.toHahn K n).fieldRange) 1)
          (RingHom.mem_fieldRange_self _ x) :
      LaurentSeries K →+* ↥(subfield K))

end PuiseuxSeries
