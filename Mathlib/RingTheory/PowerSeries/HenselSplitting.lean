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
  degree `m` whose reduction has `0` as a root of multiplicity `k` with `0 < k ≤ m` factors as
  `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`, and the reduction of `g` is `X ^ k`.

- `Polynomial.Monic.exists_factorization_rootMultiplicity`: a monic `p` over `K⟦X⟧` of degree
  `m` whose reduction has a root `a : K` of multiplicity `k` with `0 < k < m` factors as
  `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`.

-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- **Hensel splitting at zero**: a monic `p` over `K⟦X⟧` of degree `m` whose reduction
(coefficientwise `PowerSeries.constantCoeff`) has `0` as a root of multiplicity `k` with
`0 < k ≤ m` factors as `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`, and `g`
distinguished: its reduction is `X ^ k`. -/
theorem Monic.exists_factorization_rootMultiplicity_zero {p : (PowerSeries K)[X]} {m k : ℕ}
    (hp : p.Monic) (hm : p.natDegree = m)
    (hk : (p.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity 0 = k)
    (_hk0 : 0 < k) (hkm : k ≤ m) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧ h.Monic ∧ p = g * h ∧
      g.natDegree = k ∧ h.natDegree = m - k ∧
      g.map (PowerSeries.constantCoeff (R := K)) = X ^ k := by
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  set A := PowerSeries K with hA
  set e := PowerSeries.residueFieldOfPowerSeries (k := K) with he
  set φ := (p : PowerSeries A).map (IsLocalRing.residue A) with hφ
  -- The residue field of `A` is `K`, so `φ` corresponds to the reduction of `p`.
  have key : φ.map e.toRingHom
      = ((p.map (PowerSeries.constantCoeff (R := K)) : K[X]) : PowerSeries K) := by
    ext n
    simp [hφ, PowerSeries.coeff_map, Polynomial.coeff_coe]
    rfl
  -- The order of the coercion of a nonzero polynomial is its root multiplicity at `0`.
  have hordK : ((p.map (PowerSeries.constantCoeff (R := K)) : K[X]) : PowerSeries K).order
      = (k : ℕ∞) := by
    have hnz : (p.map (PowerSeries.constantCoeff (R := K))) ≠ 0 := (hp.map _).ne_zero
    rw [← hk, Polynomial.rootMultiplicity_eq_natTrailingDegree', PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => by simpa using Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi⟩
    simpa [Polynomial.trailingCoeff] using
      (Polynomial.trailingCoeff_nonzero_iff_nonzero
        (p := p.map (PowerSeries.constantCoeff (R := K)))).mpr hnz
  have hmap : (φ.map e.toRingHom).order = φ.order := by
    refine le_antisymm ?_ (PowerSeries.le_order_map _)
    have h : (φ.map e.toRingHom).map e.symm.toRingHom = φ := by ext n; simp
    have h2 := PowerSeries.le_order_map (φ := φ.map e.toRingHom) e.symm.toRingHom
    rwa [h] at h2
  have horder : φ.order = (k : ℕ∞) := by rw [← hmap, key, hordK]
  have hφnz : φ ≠ 0 := by
    intro h
    rw [h, PowerSeries.order_zero] at horder
    exact absurd horder (by simp)
  -- Weierstrass preparation for `A⟦X⟧`.
  obtain ⟨f, u, H⟩ := PowerSeries.exists_isWeierstrassFactorization hφnz
  have hfmonic : f.Monic := H.isDistinguishedAt.monic
  have hfdeg : f.natDegree = k := by
    rw [H.natDegree_eq_toNat_order_map, ← hφ, horder]; exact ENat.toNat_coe k
  have hnotMem : PowerSeries.constantCoeff (1 : PowerSeries A) ∉ IsLocalRing.maximalIdeal A := by
    simp
  have hordf : ((f : PowerSeries A).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).order = (k : ℕ∞) := by
    rw [← H.isDistinguishedAt.coe_natDegree_eq_order_map (f : PowerSeries A) 1 hnotMem
      (by simp), hfdeg]
  have Hd : PowerSeries.IsWeierstrassDivisorAt (f : PowerSeries A)
      (IsLocalRing.maximalIdeal A) := H.isDistinguishedAt.isWeierstrassDivisorAt'
  -- Divide `p` by the monic `f` in `A[X]`; uniqueness of Weierstrass division forces `u = p /ₘ f`.
  have hdivmod : p = f * (p /ₘ f) + (p %ₘ f) := by
    have h := Polynomial.modByMonic_add_div p f
    linear_combination -h
  have hrdeg : (p %ₘ f).degree < (k : ℕ) := by
    have h := Polynomial.degree_modByMonic_lt p hfmonic
    rwa [Polynomial.degree_eq_natDegree hfmonic.ne_zero, hfdeg] at h
  have heq : (f : PowerSeries A) * u + ((0 : (PowerSeries K)[X]) : PowerSeries A)
      = (f : PowerSeries A) * ((p /ₘ f : (PowerSeries K)[X]) : PowerSeries A)
        + ((p %ₘ f : (PowerSeries K)[X]) : PowerSeries A) :=
    calc (f : PowerSeries A) * u + ((0 : (PowerSeries K)[X]) : PowerSeries A)
        = (p : PowerSeries A) := by
          simp only [Polynomial.coe_zero, add_zero]; exact H.eq_mul.symm
      _ = ((f * (p /ₘ f) + p %ₘ f : (PowerSeries K)[X]) : PowerSeries A) := by rw [← hdivmod]
      _ = _ := by push_cast; ring
  have huniq := Hd.eq_of_mul_add_eq_mul_add (q := u)
    (q' := ((p /ₘ f : (PowerSeries K)[X]) : PowerSeries A))
    (r := 0) (r' := p %ₘ f) (by simp [hordf]) (by rw [hordf]; simpa using hrdeg) heq
  rw [huniq.2.symm, add_zero] at hdivmod
  have hqmonic : (p /ₘ f).Monic := hfmonic.of_mul_monic_left (hdivmod ▸ hp)
  refine ⟨f, p /ₘ f, hfmonic, hqmonic, hdivmod, hfdeg, ?_, ?_⟩
  · have hdeg := hfmonic.natDegree_mul hqmonic
    rw [← hdivmod, hm, hfdeg] at hdeg
    omega
  · -- `f` is distinguished of degree `k`, so its reduction is `X ^ k`.
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i f.natDegree with h | h | h
    · have h0 : PowerSeries.constantCoeff (R := K) (f.coeff i) = 0 := by
        rw [← RingHom.mem_ker, PowerSeries.ker_coeff_eq_max_ideal]
        exact H.isDistinguishedAt.mem h
      rw [h0, if_neg (by omega)]
    · rw [h, hfmonic.coeff_natDegree, if_pos (by omega), map_one]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, if_neg (by omega), map_zero]

/-- **Hensel splitting at a root**: a monic `p` over `K⟦X⟧` of degree `m` whose reduction
(coefficientwise `PowerSeries.constantCoeff`) has a root `a : K` of multiplicity `k` with
`0 < k < m` factors as `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`. -/
theorem Monic.exists_factorization_rootMultiplicity {p : (PowerSeries K)[X]} {m k : ℕ} {a : K}
    (hp : p.Monic) (hm : p.natDegree = m)
    (hk : (p.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity a = k)
    (hk0 : 0 < k) (hkm : k < m) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧ h.Monic ∧ p = g * h ∧
      g.natDegree = k ∧ h.natDegree = m - k := by
  set c : PowerSeries K := PowerSeries.C a with hc
  -- Shift the root to `0`.
  have hPmonic : (p.comp (X + C c)).Monic := hp.comp_X_add_C c
  have hPdeg : (p.comp (X + C c)).natDegree = m := by
    rw [← Polynomial.taylor_apply, Polynomial.natDegree_taylor, hm]
  have hred : (p.comp (X + C c)).map (PowerSeries.constantCoeff (R := K))
      = (p.map (PowerSeries.constantCoeff (R := K))).comp (X + C a) := by
    rw [Polynomial.map_comp]
    simp [hc]
  have hkP : ((p.comp (X + C c)).map
      (PowerSeries.constantCoeff (R := K))).rootMultiplicity 0 = k := by
    rw [hred, Polynomial.rootMultiplicity_eq_natTrailingDegree',
      ← Polynomial.rootMultiplicity_eq_natTrailingDegree, hk]
  obtain ⟨g₀, h₀, hg₀, hh₀, hpr, hg₀deg, hh₀deg, -⟩ :=
    hPmonic.exists_factorization_rootMultiplicity_zero hPdeg hkP hk0 hkm.le
  -- Shift back.
  have hshift : ∀ q : (PowerSeries K)[X], (q.comp (X + C c)).comp (X - C c) = q := by
    intro q
    rw [Polynomial.comp_assoc]
    simp
  have hdegsub : ∀ q : (PowerSeries K)[X], (q.comp (X - C c)).natDegree = q.natDegree := by
    intro q
    rw [show (X - C c : (PowerSeries K)[X]) = X + C (-c) by
      rw [map_neg, sub_eq_add_neg], ← Polynomial.taylor_apply, Polynomial.natDegree_taylor]
  refine ⟨g₀.comp (X - C c), h₀.comp (X - C c), hg₀.comp_X_sub_C c, hh₀.comp_X_sub_C c, ?_,
    by rw [hdegsub, hg₀deg], by rw [hdegsub, hh₀deg]⟩
  rw [← Polynomial.mul_comp, ← hpr, hshift]

end Polynomial
