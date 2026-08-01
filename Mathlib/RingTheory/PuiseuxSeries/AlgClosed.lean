/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.HenselSplitting
public import Mathlib.RingTheory.PuiseuxSeries.Algebraic
public import Mathlib.RingTheory.PuiseuxSeries.Basic

/-!
# Puiseux's theorem

This file proves **Puiseux's theorem**: over an algebraically closed field `K` of characteristic
zero, the field `PuiseuxSeries K = ⋃ n, K((t ^ (1 / n)))` of Puiseux series is algebraically
closed, and is an algebraic closure of the Laurent series field `K((t))`.

The proof is the classical Newton–Puiseux algorithm, organized as a strong induction on the
degree. Given a monic polynomial `p` of degree `m` over `K((t))`:

* a Tschirnhausen substitution `X ↦ X + c` kills the coefficient of degree `m - 1`
  (this is where characteristic zero enters);
* if all lower coefficients vanish the polynomial is `X ^ m`, with root `0`;
* otherwise, rescaling the variable by a monomial `t ^ (a / (nq))` chosen by the minimal Newton
  slope produces a monic polynomial `P` over `K⟦t⟧` whose reduction mod `t` is not a pure power
  (an internal rescaling lemma);
* the reduction of `P` has a root of multiplicity strictly between `0` and `m`, so the Hensel
  splitting `Polynomial.Monic.exists_factorization_rootMultiplicity` produces a proper monic
  factor, and the induction hypothesis applies to it at a finer index (an internal descent
  lemma).

## Main results

* `PuiseuxSeries.exists_root_mem_subfield`: every monic polynomial of positive degree over
  `K((t))`, mapped along any embedding `LaurentSeries.toHahnSeries K n`, has a root in the Puiseux
  subfield of `HahnSeries ℚ K`.
* `PuiseuxSeries.isAlgClosed`: `PuiseuxSeries K` is algebraically closed for `K` algebraically
  closed of characteristic zero.
* `PuiseuxSeries.isAlgClosure`: **Puiseux's theorem** — `PuiseuxSeries K` is an algebraic closure
  of `LaurentSeries K`.

## References

* [D. Eisenbud, *Commutative Algebra with a view toward Algebraic Geometry*][Eisenbud1995],
  Corollary 13.15

## Tags

puiseux series, newton polygon, algebraically closed, algebraic closure
-/

@[expose] public section

open Polynomial

noncomputable section

/-! ## Auxiliary polynomial lemmas -/

namespace Polynomial

private theorem Monic.tschirnhausen {F : Type*} [Field F] {p : F[X]} {m : ℕ} (hp : p.Monic)
    (hm : p.natDegree = m) (hmF : (m : F) ≠ 0) :
    (p.comp (X + C (-p.coeff (m - 1) / (m : F)))).coeff (m - 1) = 0 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmF
  set b : F := -p.coeff (m - 1) / (m : F)
  rw [← taylor_apply, taylor_coeff]
  have hdeg : ((hasseDeriv (m - 1)) p).natDegree < 2 :=
    lt_of_le_of_lt (natDegree_hasseDeriv_le p (m - 1)) (by rw [hm]; omega)
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, hasseDeriv_coeff, hasseDeriv_coeff,
    show 1 + (m - 1) = m by omega]
  simp only [Nat.choose_symm (Nat.one_le_iff_ne_zero.mpr hm0), Nat.choose_one_right,
    show p.coeff m = 1 from hm ▸ hp.coeff_natDegree, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul, mul_one, pow_zero, pow_one, b]
  field_simp
  ring

private theorem Monic.exists_rootMultiplicity_pos_lt {K : Type*} [Field K] [IsAlgClosed K]
    {r : K[X]} {m : ℕ} (hr : r.Monic) (hm : r.natDegree = m) (hmK : (m : K) ≠ 0)
    (hsub : r.coeff (m - 1) = 0) (hne : r ≠ X ^ m) :
    ∃ a : K, 0 < r.rootMultiplicity a ∧ r.rootMultiplicity a < m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmK
  have hr0 : r ≠ 0 := hr.ne_zero
  obtain ⟨a, ha⟩ :=
    IsAlgClosed.exists_root r (by rw [degree_eq_natDegree hr0, hm]; exact Nat.cast_ne_zero.mpr hm0)
  refine ⟨a, (rootMultiplicity_pos hr0).2 ha, ?_⟩
  by_contra hlt
  have heq : r = (X - C a) ^ m :=
    eq_of_monic_of_dvd_of_natDegree_le ((monic_X_sub_C a).pow m) hr
      (dvd_trans (pow_dvd_pow _ (Nat.le_of_not_lt hlt)) (pow_rootMultiplicity_dvd r a))
      (by simp [hm])
  have hz : m • (-a) = 0 := by
    rw [← nextCoeff_X_sub_C a, ← (monic_X_sub_C a).nextCoeff_pow, ← heq,
      nextCoeff_of_natDegree_pos (by omega), hm, hsub]
  rw [nsmul_eq_mul, mul_neg, neg_eq_zero, mul_eq_zero] at hz
  exact hne (by simpa [hz.resolve_left hmK] using heq)

end Polynomial

/-! ## The Newton slope rescaling and descent -/

namespace LaurentSeries

variable {K : Type*} [Field K]

private theorem toHahnSeries_expand_single_scaling (n q : ℕ+) (a : ℤ) (c : LaurentSeries K)
    (i m : ℕ) :
    HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℚ)) (1 : K) ^ m *
        toHahnSeries K (n * q) (expand q c * HahnSeries.single (a * ((i : ℤ) - m)) 1) =
      toHahnSeries K n c * HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℚ)) (1 : K) ^ i := by
  rw [map_mul, ← RingHom.comp_apply (toHahnSeries K (n * q)) (expand q),
    toHahnSeries_comp_expand, toHahnSeries_single, HahnSeries.single_pow, HahnSeries.single_pow,
    mul_left_comm, HahnSeries.single_mul_single]
  simp only [one_pow, mul_one, nsmul_eq_mul]
  congr 1
  push_cast
  ring_nf

private theorem orderTop_expand_mul_single (q : ℕ+) {c : LaurentSeries K} (hc : c ≠ 0) (k : ℤ) :
    (expand q c * HahnSeries.single k (1 : K)).orderTop =
      (((q : ℤ) * c.order + k : ℤ) : WithTop ℤ) := by
  simp [HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hc]

private theorem orderTop_expand_mul_single_nonneg (q : ℕ+) (c : LaurentSeries K) (k : ℤ)
    (h : c ≠ 0 → 0 ≤ (q : ℤ) * c.order + k) :
    0 ≤ (expand q c * HahnSeries.single k (1 : K)).orderTop := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [orderTop_expand_mul_single q hc]
    exact_mod_cast h hc

/-- Choosing `i₀` of minimal Newton slope makes the orders of the rescaled coefficients
nonnegative. -/
private theorem newton_slope_min_le {p : Polynomial (LaurentSeries K)} {m i₀ : ℕ} (hi₀m : i₀ < m)
    (hmin : ∀ i < m, p.coeff i ≠ 0 →
      ((p.coeff i₀).order : ℚ) / (m - i₀ : ℕ) ≤ ((p.coeff i).order : ℚ) / (m - i : ℕ))
    {i : ℕ} (him : i < m) (hci : p.coeff i ≠ 0) :
    0 ≤ ((m : ℤ) - i₀) * (p.coeff i).order +
      (p.coeff i₀).order * ((i : ℤ) - m) := by
  have h := hmin i him hci
  rw [div_le_div_iff₀ (mod_cast Nat.zero_lt_sub_of_lt hi₀m : (0 : ℚ) < _)
    (mod_cast Nat.zero_lt_sub_of_lt him : (0 : ℚ) < _)] at h
  push_cast [Nat.cast_sub him.le, Nat.cast_sub hi₀m.le] at h
  nlinarith [show (p.coeff i₀).order * ((m : ℤ) - i) ≤ (p.coeff i).order * ((m : ℤ) - i₀) by
    exact_mod_cast h]

/-- A family `d` of Laurent series of nonnegative order with `d m = 1` and `d (m - 1) = 0`
lifts to a monic polynomial of degree `m` over `K⟦X⟧`, with nonzero reduction at `i₀` when
`d i₀` has order zero. -/
private theorem exists_integral_poly_of_orderTop_nonneg {m i₀ : ℕ} (d : ℕ → LaurentSeries K)
    (hdnn : ∀ i : ℕ, 0 ≤ (d i).orderTop) (hdm : d m = 1) (hdm1 : d (m - 1) = 0)
    (hi₀m : i₀ ≤ m) (hd₀ : (d i₀).orderTop = 0) :
    ∃ P : Polynomial (PowerSeries K), P.Monic ∧ P.natDegree = m ∧
      (P.map (PowerSeries.constantCoeff (R := K))).coeff (m - 1) = 0 ∧
      (P.map (PowerSeries.constantCoeff (R := K))).coeff i₀ ≠ 0 ∧
      ∀ i ≤ m, HahnSeries.ofPowerSeries ℤ K (P.coeff i) = d i := by
  classical
  choose D hD using fun i ↦ mem_range_ofPowerSeries_iff.mpr (hdnn i)
  have hDm : D m = 1 := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa [hdm] using hD m)
  have hDm1 : D (m - 1) = 0 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa [hdm1] using hD (m - 1))
  have hPcoeff (j) :
      (∑ i ∈ Finset.range (m + 1), Polynomial.monomial i (D i)).coeff j =
        if j ≤ m then D j else 0 := by
    simp [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq']
  set P : Polynomial (PowerSeries K) := ∑ i ∈ Finset.range (m + 1), Polynomial.monomial i (D i)
  have hPm : P.coeff m = 1 := by rw [hPcoeff, if_pos le_rfl, hDm]
  have hle : P.natDegree ≤ m := Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN ↦ by
    rw [hPcoeff, if_neg (Nat.not_le_of_lt hN)]
  refine ⟨P, Polynomial.monic_of_natDegree_le_of_coeff_eq_one m hle hPm,
    le_antisymm hle (le_natDegree_of_ne_zero (hPm ▸ one_ne_zero)), ?_, ?_,
    fun i hi ↦ by rw [hPcoeff, if_pos hi, hD i]⟩
  · rw [Polynomial.coeff_map, hPcoeff, if_pos (Nat.sub_le _ _), hDm1, map_zero]
  · rw [Polynomial.coeff_map, hPcoeff, if_pos hi₀m]
    have := HahnSeries.coeff_orderTop_ne hd₀
    rw [← hD i₀] at this
    convert this
    simpa using (LaurentSeries.coeff_coe_powerSeries (D i₀) 0).symm

/-- If the coefficients of `P` are the rescaled coefficients of `p`, then evaluating
`p.map (toHahnSeries K n)` at `τ * y` equals `τ ^ m` times evaluating the image of `P` at `y`. -/
private theorem eval_map_toHahnSeries_of_coeff (n q : ℕ+) (a : ℤ)
    {p : Polynomial (LaurentSeries K)} {P : Polynomial (PowerSeries K)} {m : ℕ}
    (hm : p.natDegree = m) (hnd : P.natDegree = m)
    (hPd : ∀ i ≤ m, HahnSeries.ofPowerSeries ℤ K (P.coeff i) =
      expand q (p.coeff i) * HahnSeries.single (a * ((i : ℤ) - m)) 1)
    (y : HahnSeries ℚ K) :
    (p.map (toHahnSeries K n)).eval (HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℚ)) 1 * y) =
      HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℚ)) 1 ^ m *
          (P.map ((toHahnSeries K (n * q)).comp (HahnSeries.ofPowerSeries ℤ K))).eval y := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hm ▸ Polynomial.natDegree_map_le)),
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hnd ▸ Polynomial.natDegree_map_le)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_map, RingHom.comp_apply,
    hPd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)), mul_pow, ← mul_assoc, ← mul_assoc,
    toHahnSeries_expand_single_scaling n q a (p.coeff i) i m]

/-- The Newton slope rescaling: `p` monic of degree `m` over `K((t))` with vanishing
subleading coefficient and some nonzero lower coefficient rescales, via the substitution
`X ↦ τ * X` with `τ = single (a / (nq)) 1` chosen by the minimal Newton slope, to a monic `P`
of degree `m` over `K⟦X⟧` whose reduction is not a pure power of `X`. -/
private theorem newton_slope_scaling (n : ℕ+) {p : Polynomial (LaurentSeries K)} {m : ℕ}
    (hp : p.Monic) (hm : p.natDegree = m) (hsub : p.coeff (m - 1) = 0)
    (hex : ∃ i < m, p.coeff i ≠ 0) :
    ∃ (q : ℕ+) (a : ℤ) (P : Polynomial (PowerSeries K)),
      P.Monic ∧ P.natDegree = m ∧
      (P.map (PowerSeries.constantCoeff (R := K))).coeff (m - 1) = 0 ∧
      (∃ i₀ < m, (P.map (PowerSeries.constantCoeff (R := K))).coeff i₀ ≠ 0) ∧
      ∀ y : HahnSeries ℚ K,
        (p.map (toHahnSeries K n)).eval
            (HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℚ)) 1 * y) =
          HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℚ)) 1 ^ m *
              (P.map ((toHahnSeries K (n * q)).comp (HahnSeries.ofPowerSeries ℤ K))).eval y := by
  classical
  -- choose `i₀` of minimal Newton slope `order (coeff i) / (m - i)`
  obtain ⟨i₁, hi₁m, hi₁⟩ := hex
  obtain ⟨i₀, hi₀S, hi₀min⟩ :=
    ((Finset.range m).filter (fun i ↦ p.coeff i ≠ 0)).exists_min_image
      (fun i ↦ ((p.coeff i).order : ℚ) / (m - i : ℕ))
      ⟨i₁, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi₁m, hi₁⟩⟩
  obtain ⟨hi₀m, hc₀⟩ : i₀ < m ∧ p.coeff i₀ ≠ 0 := by
    simpa [Finset.mem_filter, Finset.mem_range] using hi₀S
  obtain ⟨q, hq⟩ : ∃ q : ℕ+, (q : ℕ) = m - i₀ := ⟨⟨m - i₀, Nat.zero_lt_sub_of_lt hi₀m⟩, rfl⟩
  set a : ℤ := (p.coeff i₀).order with ha
  have hqZ : (q : ℤ) = (m : ℤ) - i₀ := by rw [hq]; omega
  have key : ∀ i, i < m → p.coeff i ≠ 0 →
      0 ≤ (q : ℤ) * (p.coeff i).order + a * ((i : ℤ) - m) := fun i him hci ↦ by
    rw [hqZ]
    exact newton_slope_min_le hi₀m
      (fun j hj hcj ↦ hi₀min j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hcj⟩)) him hci
  -- the rescaled coefficient family, with slopes shifted so every order is nonnegative
  let d : ℕ → LaurentSeries K := fun i ↦
    expand q (p.coeff i) * HahnSeries.single (a * ((i : ℤ) - m)) 1
  have hdm : d m = 1 := by
    simp [d, show p.coeff m = 1 from hm ▸ hp.coeff_natDegree, -expand_apply]
  have hdz {i} (hi : p.coeff i = 0) : d i = 0 := by simp [d, hi]
  have hdnn (i : ℕ) : 0 ≤ (d i).orderTop := by
    refine orderTop_expand_mul_single_nonneg q _ _ fun hci ↦ ?_
    rcases eq_or_lt_of_le (hm ▸ Polynomial.le_natDegree_of_ne_zero hci) with heq | hlt
    · simp [heq, show p.coeff m = 1 from hm ▸ hp.coeff_natDegree]
    · exact key i hlt hci
  have hd₀ : (d i₀).orderTop = 0 := by
    rw [show d i₀ =
        expand q (p.coeff i₀) * HahnSeries.single (a * ((i₀ : ℤ) - m)) 1 from rfl,
      orderTop_expand_mul_single q hc₀, hqZ, ha]
    ring_nf
    simp
  -- lift `d` to a monic polynomial over `K⟦X⟧` and transport the evaluation identity
  obtain ⟨P, hmon, hnd, hPsub, hPi₀, hPd⟩ :=
    exists_integral_poly_of_orderTop_nonneg d hdnn hdm (hdz hsub) hi₀m.le hd₀
  exact ⟨q, a, P, hmon, hnd, hPsub, ⟨i₀, hi₀m, hPi₀⟩,
    eval_map_toHahnSeries_of_coeff n q a hm hnd hPd⟩

/-- The descent step: for `p'` monic of degree `m` over `K((t))` with vanishing subleading
coefficient and some nonzero lower coefficient, every root `y` of a proper monic factor
`g.map (toHahnSeries K (n * q))` yields the root `τ * y` of `p'.map (toHahnSeries K n)`. -/
private theorem newton_puiseux_descent [IsAlgClosed K] [CharZero K] (n : ℕ+)
    {p' : Polynomial (LaurentSeries K)} {m : ℕ}
    (hp : p'.Monic) (hm : p'.natDegree = m) (hsub : p'.coeff (m - 1) = 0)
    (hex : ∃ i < m, p'.coeff i ≠ 0) :
    ∃ (q : ℕ+) (τ : HahnSeries ℚ K) (g : Polynomial (LaurentSeries K)),
      τ ∈ (toHahnSeries K (n * q)).fieldRange ∧ g.Monic ∧
      1 ≤ g.natDegree ∧ g.natDegree < m ∧
      ∀ y : HahnSeries ℚ K,
        (g.map (toHahnSeries K (n * q))).eval y = 0 →
        (p'.map (toHahnSeries K n)).eval (τ * y) = 0 := by
  obtain ⟨q, a, P, hPm, hPdeg, hRsub, hRex, hev⟩ := newton_slope_scaling n hp hm hsub hex
  set R := P.map (PowerSeries.constantCoeff (R := K))
  have hRmonic : R.Monic := hPm.map _
  have hRdeg : R.natDegree = m := by rw [hPm.natDegree_map, hPdeg]
  have hRne : R ≠ X ^ m :=
    hRex.elim fun i₀ ⟨hi₀, hne⟩ h ↦ by simp [h, Polynomial.coeff_X_pow, hi₀.ne] at hne
  obtain ⟨a₀, hk0, hkm⟩ := hRmonic.exists_rootMultiplicity_pos_lt hRdeg
    (Nat.cast_ne_zero.mpr (hex.elim fun _ ⟨hi, _⟩ ↦ (Nat.zero_lt_of_lt hi).ne')) hRsub hRne
  obtain ⟨G, h, hG, hh, hPeq, hGdeg, -⟩ :=
    hPm.exists_factorization_rootMultiplicity (a := a₀) hPdeg rfl
  refine ⟨q, HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℚ)) 1,
    G.map (HahnSeries.ofPowerSeries ℤ K), ⟨HahnSeries.single a 1, by rw [toHahnSeries_single]⟩,
    hG.map _, ?_, ?_, ?_⟩
  · rw [hG.natDegree_map, hGdeg]; exact hk0
  · rw [hG.natDegree_map, hGdeg]; exact hkm
  · intro y hy
    rw [hev y, ← Polynomial.map_map, hPeq, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.eval_mul, hy, zero_mul, mul_zero]

end LaurentSeries

namespace PuiseuxSeries

open LaurentSeries

variable {K : Type*} [Field K]

/-! ## The Newton–Puiseux induction and main results -/

/-- The Newton–Puiseux induction, in the form suitable for strong induction on the degree:
the statement is quantified over all indices `n`, since the descent step re-enters at a finer
index. -/
private theorem exists_root_mem_subfield_aux [IsAlgClosed K] [CharZero K] :
    ∀ m : ℕ, ∀ (n : ℕ+) (p : Polynomial (LaurentSeries K)), p.Monic → p.natDegree = m →
      1 ≤ m → ∃ x ∈ PuiseuxSeries.subfield K, (p.map (toHahnSeries K n)).eval x = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n p hp hm hm1
  have : CharZero (LaurentSeries K) :=
    charZero_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective
  have hmF : (m : LaurentSeries K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hm1)
  set b : LaurentSeries K := -p.coeff (m - 1) / (m : LaurentSeries K)
  set p' : Polynomial (LaurentSeries K) := p.comp (X + C b) with hp'def
  have hp'm : p'.Monic := hp.comp_X_add_C b
  have hp'deg : p'.natDegree = m := by rw [hp'def, ← taylor_apply, natDegree_taylor, hm]
  have hp'sub : p'.coeff (m - 1) = 0 := hp.tschirnhausen hm hmF
  obtain ⟨y, hy, hy0⟩ : ∃ y ∈ PuiseuxSeries.subfield K, (p'.map (toHahnSeries K n)).eval y = 0 := by
    by_cases hex : ∃ i < m, p'.coeff i ≠ 0
    · obtain ⟨q, τ, g, hτ, hg, hg1, hgm, htrans⟩ :=
        newton_puiseux_descent n hp'm hp'deg hp'sub hex
      obtain ⟨y, hy, hy0⟩ := ih g.natDegree hgm (n * q) g hg rfl hg1
      exact ⟨τ * y, mul_mem ((PuiseuxSeries.mem_subfield_iff K).mpr ⟨n * q, hτ⟩) hy,
        htrans y hy0⟩
    · have h0 : p'.coeff 0 = 0 := by_contra fun hne ↦ hex ⟨0, hm1, hne⟩
      exact ⟨0, zero_mem _, by
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, h0, map_zero]⟩
  refine ⟨y + toHahnSeries K n b,
    add_mem hy ((PuiseuxSeries.mem_subfield_iff K).mpr ⟨n, b, rfl⟩), ?_⟩
  simpa [hp'def, Polynomial.map_comp, Polynomial.eval_comp] using hy0

/-- For `K` algebraically closed of characteristic zero, every monic polynomial over `K((t))`
of positive degree, mapped along any embedding `toHahnSeries K n`, has a root in the Puiseux
subfield. -/
theorem exists_root_mem_subfield [IsAlgClosed K] [CharZero K] (n : ℕ+)
    {p : Polynomial (LaurentSeries K)} (hp : p.Monic) (hdeg : 1 ≤ p.natDegree) :
    ∃ x ∈ PuiseuxSeries.subfield K, (p.map (toHahnSeries K n)).eval x = 0 :=
  exists_root_mem_subfield_aux p.natDegree n p hp rfl hdeg

/-- For `K` an algebraically closed field of characteristic zero, the field of Puiseux series
over `K` is algebraically closed. -/
instance isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    IsAlgClosed (PuiseuxSeries K) := by
  apply IsAlgClosed.of_exists_root
  intro r hr hirr
  classical
  set ι : PuiseuxSeries K →+* HahnSeries ℚ K := (PuiseuxSeries.subfield K).subtype
  have hιinj : Function.Injective ι := Subtype.val_injective
  -- push all coefficients of `r` into the range of a single `toHahnSeries K N`
  obtain ⟨N, hN⟩ :=
    PuiseuxSeries.exists_common_index K
      ((Finset.range (r.natDegree + 1)).image fun i ↦ (r.map ι).coeff i)
      (fun x hx ↦ by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact (Polynomial.coeff_map ι i).symm ▸ (r.coeff i).2)
  have hrange : ∀ i, (r.map ι).coeff i ∈ Set.range (LaurentSeries.toHahnSeries K N) := by
    intro i
    by_cases hi : i ≤ r.natDegree
    · exact Set.mem_range.mpr
        (hN _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩))
    · exact ⟨0, by rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [hr.natDegree_map]; exact Nat.lt_of_not_le hi)]⟩
  -- lift to a monic polynomial over `K((t))` and take its Puiseux root
  obtain ⟨p, hpmap, hpdeg, hpm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts _).mpr hrange) (hr.map ι)
  have hdeg : 1 ≤ p.natDegree := by
    rw [natDegree_eq_of_degree_eq hpdeg, hr.natDegree_map]; exact hirr.natDegree_pos
  obtain ⟨x, hx, hx0⟩ := exists_root_mem_subfield N hpm hdeg
  refine ⟨⟨x, hx⟩, hιinj (by
    rw [map_zero, ← hx0, hpmap]
    exact (Polynomial.eval₂_hom ι (⟨x, hx⟩ : PuiseuxSeries K)).symm.trans
      (Polynomial.eval_map ι x).symm)⟩

/-- **Puiseux's theorem**: for `K` an algebraically closed field of characteristic zero, the
Puiseux series field `⋃ n, K((t ^ (1 / n)))` is an algebraic closure of the Laurent series
field `K((t))`. -/
instance isAlgClosure (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    IsAlgClosure (LaurentSeries K) (PuiseuxSeries K) :=
  ⟨inferInstance, inferInstance⟩

end PuiseuxSeries
