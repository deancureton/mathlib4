/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Hensel splitting for polynomials over power series

In this file we derive from the Weierstrass preparation theorem
(`PowerSeries.exists_isWeierstrassFactorization`) a Hensel-style splitting for a monic
polynomial `p` over `K⟦X⟧`: a root of multiplicity `k` of the reduction of `p` modulo the
maximal ideal of `K⟦X⟧` (that is, of the coefficientwise application of
`PowerSeries.constantCoeff` to `p`) lifts to a monic factor of `p` of degree `k`.

## Main results

- `Polynomial.Monic.exists_factorization_rootMultiplicity_zero`: a monic `p` over `K⟦X⟧` of
  degree `m` whose reduction has `0` as a root of multiplicity `k` factors as
  `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`, and the reduction of `g` is `X ^ k`.

- `Polynomial.Monic.exists_factorization_rootMultiplicity`: a monic `p` over `K⟦X⟧` of degree
  `m` whose reduction has a root `a : K` of multiplicity `k` factors as
  `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`, and the reduction of `g` is
  `(X - C a) ^ k`.

-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- A monic `p` over `K⟦X⟧` of degree `m` whose reduction
(coefficientwise `PowerSeries.constantCoeff`) has `0` as a root of multiplicity `k`
factors as `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`, and `g`
distinguished: its reduction is `X ^ k`. -/
theorem Monic.exists_factorization_rootMultiplicity_zero {p : (PowerSeries K)[X]} {m k : ℕ}
    (hp : p.Monic) (hm : p.natDegree = m)
    (hk : (p.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity 0 = k) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧ h.Monic ∧ p = g * h ∧
      g.natDegree = k ∧ h.natDegree = m - k ∧
      g.map (PowerSeries.constantCoeff (R := K)) = X ^ k := by
  have hkm : k ≤ m := by
    rw [← hk, Polynomial.rootMultiplicity_eq_natTrailingDegree', ← hm,
      ← hp.natDegree_map (PowerSeries.constantCoeff (R := K))]
    exact Polynomial.natTrailingDegree_le_natDegree _
  have : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  set A := PowerSeries K
  set e := PowerSeries.residueFieldOfPowerSeries (k := K)
  set φ := (p : PowerSeries A).map (IsLocalRing.residue A) with hφ
  have key (n : ℕ) : e (PowerSeries.coeff n φ) =
      (p.map (PowerSeries.constantCoeff (R := K))).coeff n := by
    simp only [hφ, PowerSeries.coeff_map, Polynomial.coeff_coe, Polynomial.coeff_map]; rfl
  have horder : φ.order = k := by
    have hnz : (p.map (PowerSeries.constantCoeff (R := K))) ≠ 0 := (hp.map _).ne_zero
    rw [← hk, Polynomial.rootMultiplicity_eq_natTrailingDegree', PowerSeries.order_eq_nat]
    refine ⟨fun h ↦ Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hnz ?_,
      fun i hi ↦ e.injective (by simp [key, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi])⟩
    rw [Polynomial.trailingCoeff, ← key, h, map_zero]
  have hφnz : φ ≠ 0 := fun h ↦ by simp [h] at horder
  obtain ⟨f, u, H⟩ := PowerSeries.exists_isWeierstrassFactorization hφnz
  have hfmonic : f.Monic := H.isDistinguishedAt.monic
  have hfdeg : f.natDegree = k := by
    rw [H.natDegree_eq_toNat_order_map, ← hφ, horder, ENat.toNat_natCast]
  have hordf : ((f : PowerSeries A).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).order = k := by
    rw [← H.isDistinguishedAt.coe_natDegree_eq_order_map (f : PowerSeries A) 1 (by simp)
      (by simp), hfdeg]
  have hdivmod : p = f * (p /ₘ f) + p %ₘ f :=
    ((add_comm _ _).trans (p.modByMonic_add_div f)).symm
  have hrdeg : (p %ₘ f).degree < k :=
    hfdeg ▸ Polynomial.degree_eq_natDegree hfmonic.ne_zero ▸ p.degree_modByMonic_lt hfmonic
  have huniq := H.isDistinguishedAt.isWeierstrassDivisorAt'.eq_of_mul_add_eq_mul_add (q := u)
    (q' := ↑(p /ₘ f)) (r := 0) (r' := p %ₘ f) (by simp [hordf]) (by rw [hordf]; simpa using hrdeg)
    (by rw [Polynomial.coe_zero, add_zero, ← H.eq_mul]
        exact_mod_cast hdivmod)
  rw [huniq.2.symm, add_zero] at hdivmod
  refine ⟨f, p /ₘ f, hfmonic, hfmonic.of_mul_monic_left (hdivmod ▸ hp), hdivmod, hfdeg, ?_, ?_⟩
  · have := p.natDegree_divByMonic hfmonic
    omega
  · have h1 := congrArg (Polynomial.map e.toRingHom)
      (show f.map (IsLocalRing.residue A) = X ^ k from hfdeg ▸ H.isDistinguishedAt.map_eq_X_pow)
    rwa [Polynomial.map_map, Polynomial.map_pow, Polynomial.map_X] at h1

/-- A monic `p` over `K⟦X⟧` of degree `m` whose reduction
(coefficientwise `PowerSeries.constantCoeff`) has a root `a : K` of multiplicity `k`
factors as `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`, and the reduction of
`g` is `(X - C a) ^ k`. -/
theorem Monic.exists_factorization_rootMultiplicity {p : (PowerSeries K)[X]} {m k : ℕ} {a : K}
    (hp : p.Monic) (hm : p.natDegree = m)
    (hk : (p.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity a = k) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧ h.Monic ∧ p = g * h ∧
      g.natDegree = k ∧ h.natDegree = m - k ∧
      g.map (PowerSeries.constantCoeff (R := K)) = (X - C a) ^ k := by
  set c : PowerSeries K := PowerSeries.C a with hc
  have hkP : ((p.comp (X + C c)).map
      (PowerSeries.constantCoeff (R := K))).rootMultiplicity 0 = k := by
    rw [show (p.comp (X + C c)).map (PowerSeries.constantCoeff (R := K)) =
        (p.map (PowerSeries.constantCoeff (R := K))).comp (X + C a) by
      simp [Polynomial.map_comp, hc], ← Polynomial.rootMultiplicity_eq_rootMultiplicity, hk]
  obtain ⟨g₀, h₀, hg₀, hh₀, hpr, hg₀deg, hh₀deg, hg₀red⟩ :=
    (hp.comp_X_add_C c).exists_factorization_rootMultiplicity_zero (m := m)
      (by simp [Polynomial.natDegree_comp, hm]) hkP
  refine ⟨g₀.comp (X - C c), h₀.comp (X - C c), hg₀.comp_X_sub_C c, hh₀.comp_X_sub_C c, ?_,
    by simp [Polynomial.natDegree_comp, hg₀deg], by simp [Polynomial.natDegree_comp, hh₀deg], ?_⟩
  · simp [← Polynomial.mul_comp, ← hpr, Polynomial.comp_assoc]
  · simp [Polynomial.map_comp, hg₀red, hc]

end Polynomial
