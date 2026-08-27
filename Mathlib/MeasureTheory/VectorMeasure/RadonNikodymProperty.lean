/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# The Radon-Nikodym property

This file defines the Radon-Nikodym property for real Banach spaces and proves that every
finite-dimensional space has this property.

## Main declarations

* `MeasureTheory.RadonNikodymProperty`: every absolutely continuous vector measure of bounded
  variation has a Bochner-integrable density.
-/

public section

noncomputable section

open scoped ENNReal MeasureTheory

namespace MeasureTheory

universe u v

/-- A Banach space has the Radon-Nikodym property if every vector measure of bounded variation
that is absolutely continuous with respect to a sigma-finite measure has a density. -/
class RadonNikodymProperty (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] : Prop where
  exists_withDensityᵥ_eq : ∀ {α : Type v} [MeasurableSpace α] (ν : VectorMeasure α E)
    (μ : Measure α) [IsFiniteMeasure ν.variation] [SigmaFinite μ],
    ν ≪ᵥ μ.toENNRealVectorMeasure →
      ∃ f : α → E, Integrable f μ ∧ μ.withDensityᵥ f = ν

namespace VectorMeasure.AbsolutelyContinuous

variable {α : Type v} {E : Type u} [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {ν : VectorMeasure α E} {μ : Measure α}

/-- An absolutely continuous vector measure with values in a space with the Radon-Nikodym
property has a Bochner-integrable density. -/
theorem exists_withDensityᵥ_eq [hE : RadonNikodymProperty.{u, v} E]
    [IsFiniteMeasure ν.variation]
    [SigmaFinite μ] (h : ν ≪ᵥ μ.toENNRealVectorMeasure) :
    ∃ f : α → E, Integrable f μ ∧ μ.withDensityᵥ f = ν :=
  hE.exists_withDensityᵥ_eq ν μ h

end VectorMeasure.AbsolutelyContinuous

namespace VectorMeasure

variable {α : Type v} {E : Type u} [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

/-- A vector measure of bounded variation with values in a space with the Radon-Nikodym property
has a Bochner-integrable density with respect to its variation. -/
theorem exists_withDensityᵥ_variation [RadonNikodymProperty.{u, v} E]
    (ν : VectorMeasure α E) [IsFiniteMeasure ν.variation] :
    ∃ f : α → E, Integrable f ν.variation ∧ ν.variation.withDensityᵥ f = ν :=
  ν.absolutelyContinuous.exists_withDensityᵥ_eq

end VectorMeasure

/-- Every finite-dimensional real normed space has the Radon-Nikodym property. -/
instance {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    RadonNikodymProperty.{u, v} E where
  exists_withDensityᵥ_eq ν μ := fun hνμ ↦ by
    let ι := Module.Basis.ofVectorSpaceIndex ℝ E
    let A : E ≃L[ℝ] (ι → ℝ) :=
      (Module.Basis.ofVectorSpace ℝ E).equivFun.toContinuousLinearEquiv
    let p (i : ι) : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp A.toContinuousLinearMap
    let νi (i : ι) : SignedMeasure _ := ν.mapRange (p i).toAddMonoidHom (p i).continuous
    have hνi (i : ι) : νi i ≪ᵥ μ.toENNRealVectorMeasure := by
      intro s hs
      change p i (ν s) = 0
      simp [hνμ hs]
    let g := fun x i ↦ SignedMeasure.rnDeriv (νi i) μ x
    have hgi (i : ι) : Integrable (fun x ↦ g x i) μ :=
      SignedMeasure.integrable_rnDeriv (νi i) μ
    have hg : Integrable g μ := Integrable.of_eval hgi
    let f := fun x ↦ A.symm (g x)
    have hf : Integrable f μ := A.symm.toContinuousLinearMap.integrable_comp hg
    refine ⟨f, hf, ?_⟩
    ext s hs
    apply A.injective
    rw [withDensityᵥ_apply hf hs, ← A.integral_comp_comm]
    simp only [f, A.apply_symm_apply]
    ext i
    rw [eval_integral (fun i ↦ (hgi i).restrict) i]
    have hi := DFunLike.congr_fun
      (SignedMeasure.withDensityᵥ_rnDeriv_eq (νi i) μ (hνi i)) s
    rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv (νi i) μ) hs] at hi
    simpa [g, νi, p] using hi

end MeasureTheory
