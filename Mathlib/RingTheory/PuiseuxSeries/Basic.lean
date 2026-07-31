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
`LaurentSeries.toHahnSeries K n : K((t)) →+* HahnSeries ℚ K` sending `t` to `t ^ (1 / n)`.

## Main definitions

* `LaurentSeries.toHahnSeries K n`: the ring embedding `K((t)) →+* HahnSeries ℚ K`
  sending `t` to `t ^ (1 / n)`.
* `PuiseuxSeries.subfield K`: the Puiseux subfield `⨆ n, (toHahnSeries K n).fieldRange` of
  `HahnSeries ℚ K`.
* `PuiseuxSeries K`: the type of Puiseux series over `K`, a field, equipped with an algebra
  structure over `LaurentSeries K` via `toHahnSeries K 1`.

## Main results

* `PuiseuxSeries.mem_subfield_iff`: a Hahn series lies in the Puiseux subfield if and only if
  it lies in the range of some `toHahnSeries K n`.
* `PuiseuxSeries.mem_subfield_iff_support`: a Hahn series lies in the Puiseux subfield if and
  only if every exponent in its support lies in `(1 / n) • ℤ` for a single `n`.
* `PuiseuxSeries.exists_common_index`: finitely many Puiseux series lie in the range of a single
  `toHahnSeries K N`.

## Tags

puiseux series, laurent series, hahn series
-/

@[expose] public section

open HahnSeries Polynomial

noncomputable section

namespace LaurentSeries

variable (K : Type*) [Field K]

/-- The ring embedding `K((t)) →+* HahnSeries ℚ K` sending `t` to `t ^ (1 / n)`, obtained by
embedding the exponents along `k ↦ k / n : ℤ → ℚ`. -/
def toHahnSeries (n : ℕ+) : LaurentSeries K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom
    (AddMonoidHom.mk' (fun k : ℤ ↦ (k : ℚ) / (n : ℚ)) fun a b ↦ by push_cast; ring)
    (fun _ _ h ↦ Int.cast_injective ((div_left_inj' (Nat.cast_ne_zero.mpr n.ne_zero)).mp h))
    fun _ _ ↦ (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr n.pos)).trans Int.cast_le

@[simp]
theorem toHahnSeries_single (n : ℕ+) (k : ℤ) (a : K) :
    toHahnSeries K n (HahnSeries.single k a) = HahnSeries.single ((k : ℚ) / (n : ℚ)) a :=
  HahnSeries.embDomain_single ..

theorem toHahnSeries_comp_expand (n m : ℕ+) :
    (toHahnSeries K (n * m)).comp (expand K m) = toHahnSeries K n :=
  RingHom.ext fun f ↦ by
    change HahnSeries.embDomain _ (HahnSeries.embDomain _ f) = HahnSeries.embDomain _ f
    rw [HahnSeries.embDomain_embDomain]
    congr 1 with k
    simp [mul_comm ((n : ℚ)), mul_div_mul_left]

theorem fieldRange_toHahnSeries_le (n m : ℕ+) :
    (toHahnSeries K n).fieldRange ≤ (toHahnSeries K (n * m)).fieldRange :=
  fun _ ⟨f, hf⟩ ↦ ⟨expand K m f, (DFunLike.congr_fun (toHahnSeries_comp_expand K n m) f).trans hf⟩

theorem directed_fieldRange_toHahnSeries :
    Directed (· ≤ ·) fun n : ℕ+ ↦ (toHahnSeries K n).fieldRange := fun a b ↦
  ⟨a * b, fieldRange_toHahnSeries_le K a b, mul_comm b a ▸ fieldRange_toHahnSeries_le K b a⟩

end LaurentSeries

namespace PuiseuxSeries

open LaurentSeries

variable (K : Type*) [Field K]

/-- The subfield of `HahnSeries ℚ K` consisting of Puiseux series, the directed union of the
ranges of the embeddings `toHahnSeries K n`. -/
def subfield : Subfield (HahnSeries ℚ K) :=
  ⨆ n : ℕ+, (toHahnSeries K n).fieldRange

theorem mem_subfield_iff {x : HahnSeries ℚ K} :
    x ∈ subfield K ↔ ∃ n : ℕ+, x ∈ (toHahnSeries K n).fieldRange :=
  Subfield.mem_iSup_of_directed (directed_fieldRange_toHahnSeries K)

/-- A Hahn series lies in the Puiseux subfield if and only if every exponent in its support
lies in `(1 / n) • ℤ` for a single `n`. -/
theorem mem_subfield_iff_support {x : HahnSeries ℚ K} :
    x ∈ subfield K ↔
      ∃ n : ℕ+, ∀ q ∈ x.support, ∃ k : ℤ, q = (k : ℚ) / (n : ℚ) := by
  rw [mem_subfield_iff]
  refine exists_congr fun n ↦ ?_
  rw [show x ∈ (toHahnSeries K n).fieldRange ↔ _ from HahnSeries.mem_range_embDomain_iff]
  exact ⟨fun h q hq ↦ (h hq).imp fun _ hk ↦ hk.symm,
    fun h q hq ↦ (h q hq).imp fun _ hk ↦ hk.symm⟩

theorem exists_common_index (s : Finset (HahnSeries ℚ K))
    (hs : ∀ x ∈ s, x ∈ subfield K) :
    ∃ N : ℕ+, ∀ x ∈ s, x ∈ (toHahnSeries K N).fieldRange := by
  choose! n hn using fun x (hx : x ∈ s) ↦ (mem_subfield_iff K).mp (hs x hx)
  obtain ⟨N, hN⟩ := (directed_fieldRange_toHahnSeries K).finset_le (s.image n)
  exact ⟨N, fun x hx ↦ hN (n x) (Finset.mem_image_of_mem n hx) (hn x hx)⟩

end PuiseuxSeries

/-- The field of Puiseux series over a field `K`, defined as the carrier of the Puiseux
subfield `PuiseuxSeries.subfield K` of `HahnSeries ℚ K`. -/
def PuiseuxSeries (K : Type*) [Field K] : Type _ :=
  ↥(PuiseuxSeries.subfield K)

namespace PuiseuxSeries

variable (K : Type*) [Field K]

instance : Field (PuiseuxSeries K) :=
  inferInstanceAs (Field ↥(subfield K))

/-- The `K((t))`-algebra structure on Puiseux series, given by `toHahnSeries K 1`
corestricted to the Puiseux subfield. -/
instance algebraLaurentSeries : Algebra (LaurentSeries K) (PuiseuxSeries K) :=
  RingHom.toAlgebra <|
    (LaurentSeries.toHahnSeries K 1).codRestrict (subfield K) fun x ↦
      (mem_subfield_iff K).mpr ⟨1, RingHom.mem_fieldRange_self _ x⟩

end PuiseuxSeries
