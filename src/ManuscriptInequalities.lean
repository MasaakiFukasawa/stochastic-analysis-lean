/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import ManuscriptMeasure
import Appendix

/-! app1:77--110. Normalize f and g by their norms, apply Young pointwise,
integrate, and undo normalization. Minkowski uses Holder on f*(f+g)^(p-1)
and g*(f+g)^(p-1), then divides by the nonzero finite norm. The missing p=1
case is explicit. Adapted from Mathlib implementations of these same arguments;
local names prevent calling the original target inequalities. -/
open ENNReal MeasureTheory Finset
namespace Asakura
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem manuscript_lintegral_rpow_div_add_rpow_div_eq_one_of_lintegral_rpow_eq_one {p q : ℝ}
    (hpq : p.HolderConjugate q) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hf_norm : ∫⁻ a, f a ^ p ∂μ = 1) (hg_norm : ∫⁻ a, g a ^ q ∂μ = 1) :
    ∫⁻ a, f a ^ p / .ofReal p + g a ^ q / .ofReal q ∂μ = 1 := by
  simp_rw [div_eq_mul_inv]
  rw [lintegral_add_left' (by fun_prop), lintegral_mul_const'' _ (hf.pow_const p),
    lintegral_mul_const', hf_norm, hg_norm, one_mul, one_mul, hpq.inv_add_inv_ennreal]
  simp [hpq.symm.pos]

/-- Hölder's inequality for functions with norm `1` -/
theorem manuscript_lintegral_mul_le_one_of_lintegral_rpow_eq_one {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_norm : ∫⁻ a, f a ^ p ∂μ = 1)
    (hg_norm : ∫⁻ a, g a ^ q ∂μ = 1) : (∫⁻ a, (f * g) a ∂μ) ≤ 1 := by
  rw [← manuscript_lintegral_rpow_div_add_rpow_div_eq_one_of_lintegral_rpow_eq_one hpq hf hf_norm hg_norm]
  exact lintegral_mono fun a ↦ young_inequality (f a) (g a) hpq


/-- Function multiplied by the inverse of its p-seminorm `(∫⁻ f^p ∂μ) ^ 1/p` -/
noncomputable def manuscript_funMulInvSnorm (f : α → ℝ≥0∞) (p : ℝ) (μ : Measure α) : α → ℝ≥0∞ := fun a =>
  f a * ((∫⁻ c, f c ^ p ∂μ) ^ (1 / p))⁻¹

theorem manuscript_fun_eq_funMulInvSnorm_mul_eLpNorm {p : ℝ} (f : α → ℝ≥0∞)
    (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) {a : α} :
    f a = manuscript_funMulInvSnorm f p μ a * (∫⁻ c, f c ^ p ∂μ) ^ (1 / p) := by
  simp [manuscript_funMulInvSnorm, mul_assoc, ENNReal.inv_mul_cancel, hf_nonzero, hf_top]

theorem manuscript_funMulInvSnorm_rpow {p : ℝ} (hp0 : 0 < p) {f : α → ℝ≥0∞} {a : α} :
    manuscript_funMulInvSnorm f p μ a ^ p = f a ^ p * (∫⁻ c, f c ^ p ∂μ)⁻¹ := by
  rw [manuscript_funMulInvSnorm, mul_rpow_of_nonneg _ _ (le_of_lt hp0)]
  suffices h_inv_rpow : ((∫⁻ c : α, f c ^ p ∂μ) ^ (1 / p))⁻¹ ^ p = (∫⁻ c : α, f c ^ p ∂μ)⁻¹ by
    rw [h_inv_rpow]
  rw [inv_rpow, ← rpow_mul, one_div_mul_cancel hp0.ne', rpow_one]

theorem manuscript_funMulInvSnorm_rpow' {p : ℝ} (hp0 : 0 < p) (f : α → ℝ≥0∞) :
    manuscript_funMulInvSnorm f p μ ^ p = (∫⁻ c, f c ^ p ∂μ)⁻¹ • f ^ p := by
  ext a
  simp [manuscript_funMulInvSnorm_rpow hp0, mul_comm]

theorem manuscript_lintegral_rpow_funMulInvSnorm_eq_one {p : ℝ} (hp0_lt : 0 < p) {f : α → ℝ≥0∞}
    (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) :
    ∫⁻ c, manuscript_funMulInvSnorm f p μ c ^ p ∂μ = 1 := by
  simp_rw [manuscript_funMulInvSnorm_rpow hp0_lt]
  rw [lintegral_mul_const', ENNReal.mul_inv_cancel hf_nonzero hf_top]
  rwa [inv_ne_top]

theorem manuscript_lintegral_mul_eq_lintegral_funMulInvSnorm_mul_funMulInvSnorm_mul_Lp_mul_Lq {p q : ℝ}
    {f g : α → ℝ≥0∞} (hf_nontop : ∫⁻ a, f a ^ p ∂μ ≠ ⊤) (hg_nontop : ∫⁻ a, g a ^ q ∂μ ≠ ⊤)
    (hf_nonzero : ∫⁻ a, f a ^ p ∂μ ≠ 0) (hg_nonzero : ∫⁻ a, g a ^ q ∂μ ≠ 0) :
    ∫⁻ a, (f * g) a ∂μ = (∫⁻ a, (manuscript_funMulInvSnorm f p μ * manuscript_funMulInvSnorm g q μ) a ∂μ) *
      ((∫⁻ c : α, f c ^ p ∂μ) ^ (1 / p) * (∫⁻ c : α, g c ^ q ∂μ) ^ (1 / q)) := by
  have : (∫⁻ (c : α), f c ^ p ∂μ) ^ (1 / p) * (∫⁻ (c : α), g c ^ q ∂μ) ^ (1 / q) ≠ ∞ := by
    grind [mul_eq_top, rpow_eq_top_iff]
  rw [← lintegral_mul_const' _ _ this]
  refine lintegral_congr fun a ↦ ?_
  rw [Pi.mul_apply, manuscript_fun_eq_funMulInvSnorm_mul_eLpNorm f hf_nonzero hf_nontop,
    manuscript_fun_eq_funMulInvSnorm_mul_eLpNorm g hg_nonzero hg_nontop, Pi.mul_apply]
  ring

/-- Hölder's inequality in case of finite non-zero integrals -/
theorem manuscript_lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_nontop : ∫⁻ a, f a ^ p ∂μ ≠ ⊤)
    (hg_nontop : ∫⁻ a, g a ^ q ∂μ ≠ ⊤) (hf_nonzero : ∫⁻ a, f a ^ p ∂μ ≠ 0)
    (hg_nonzero : ∫⁻ a, g a ^ q ∂μ ≠ 0) :
    ∫⁻ a, (f * g) a ∂μ ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  rw [manuscript_lintegral_mul_eq_lintegral_funMulInvSnorm_mul_funMulInvSnorm_mul_Lp_mul_Lq hf_nontop hg_nontop
      hf_nonzero hg_nonzero]
  apply mul_le_of_le_one_left'
  have hf1 := manuscript_lintegral_rpow_funMulInvSnorm_eq_one hpq.pos hf_nonzero hf_nontop
  have hg1 := manuscript_lintegral_rpow_funMulInvSnorm_eq_one hpq.symm.pos hg_nonzero hg_nontop
  exact manuscript_lintegral_mul_le_one_of_lintegral_rpow_eq_one hpq (hf.mul_const _) hf1 hg1


theorem manuscript_ae_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0 : 0 ≤ p) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_zero : ∫⁻ a, f a ^ p ∂μ = 0) : f =ᵐ[μ] 0 := by
  rw [lintegral_eq_zero_iff' (hf.pow_const p)] at hf_zero
  filter_upwards [hf_zero] with x
  rw [Pi.zero_apply, ← not_imp_not]
  exact fun hx => (rpow_pos_of_nonneg (pos_iff_ne_zero.2 hx) hp0).ne'

theorem manuscript_lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0 : 0 ≤ p) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_zero : ∫⁻ a, f a ^ p ∂μ = 0) : (∫⁻ a, (f * g) a ∂μ) = 0 := by
  rw [← @lintegral_zero_fun α _ μ]
  refine lintegral_congr_ae ?_
  suffices h_mul_zero : f * g =ᵐ[μ] 0 * g by rwa [zero_mul] at h_mul_zero
  have hf_eq_zero : f =ᵐ[μ] 0 := manuscript_ae_eq_zero_of_lintegral_rpow_eq_zero hp0 hf hf_zero
  exact hf_eq_zero.mul (ae_eq_refl g)

theorem manuscript_lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top {p q : ℝ} (hp0_lt : 0 < p) (hq0 : 0 ≤ q)
    {f g : α → ℝ≥0∞} (hf_top : ∫⁻ a, f a ^ p ∂μ = ⊤) (hg_nonzero : (∫⁻ a, g a ^ q ∂μ) ≠ 0) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  simp [*]

/-- Hölder's inequality for functions `α → ℝ≥0∞`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem manuscript_lintegral_mul_le_Lp_mul_Lq (μ : Measure α) {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  by_cases hf_zero : ∫⁻ a, f a ^ p ∂μ = 0
  · refine Eq.trans_le ?_ zero_le
    exact manuscript_lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.nonneg hf hf_zero
  by_cases hg_zero : ∫⁻ a, g a ^ q ∂μ = 0
  · refine Eq.trans_le ?_ zero_le
    rw [mul_comm]
    exact manuscript_lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.symm.nonneg hg hg_zero
  by_cases hf_top : ∫⁻ a, f a ^ p ∂μ = ⊤
  · exact manuscript_lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.pos hpq.symm.nonneg hf_top hg_zero
  by_cases hg_top : ∫⁻ a, g a ^ q ∂μ = ⊤
  · rw [mul_comm, mul_comm ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p))]
    exact manuscript_lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.symm.pos hpq.nonneg hg_top hf_zero
  -- non-⊤ non-zero case
  exact manuscript_lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top hpq hf hf_top hg_top hf_zero hg_zero


theorem manuscript_lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top {p : ℝ} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_top : (∫⁻ a, f a ^ p ∂μ) < ⊤) (hg_top : (∫⁻ a, g a ^ p ∂μ) < ⊤)
    (hp1 : 1 ≤ p) : (∫⁻ a, (f + g) a ^ p ∂μ) < ⊤ := by
  calc
    (∫⁻ a : α, (f a + g a) ^ p ∂μ) ≤
        ∫⁻ a, (2 : ℝ≥0∞) ^ (p - 1) * f a ^ p + (2 : ℝ≥0∞) ^ (p - 1) * g a ^ p ∂μ := by
      refine lintegral_mono fun a => ?_
      simpa [mul_add] using ENNReal.rpow_add_le_mul_rpow_add_rpow (f a) (g a) hp1
    _ < ⊤ := by
      rw [lintegral_add_left', lintegral_const_mul'' _ (hf.pow_const p),
        lintegral_const_mul' _ _ (by finiteness), ENNReal.add_lt_top]
      · constructor <;> finiteness
      · fun_prop


theorem manuscript_lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow {p q : ℝ}
    (hpq : p.HolderConjugate q) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a * g a ^ (p - 1) ∂μ ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ p ∂μ) ^ (1 / q) := by
  refine (manuscript_lintegral_mul_le_Lp_mul_Lq μ hpq hf (hg.pow_const _)).trans_eq ?_
  simp [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]

theorem manuscript_lintegral_rpow_add_le_add_eLpNorm_mul_lintegral_rpow_add {p q : ℝ}
    (hpq : p.HolderConjugate q) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, (f + g) a ^ p ∂μ ≤
      ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) *
        (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q) := by
  calc
    (∫⁻ a, (f + g) a ^ p ∂μ) ≤ ∫⁻ a, (f + g) a * (f + g) a ^ (p - 1) ∂μ := by
      gcongr with a
      by_cases h_zero : (f + g) a = 0
      · rw [h_zero, ENNReal.zero_rpow_of_pos hpq.pos]
        exact zero_le
      by_cases h_top : (f + g) a = ⊤
      · rw [h_top, ENNReal.top_rpow_of_pos hpq.sub_one_pos, ENNReal.top_mul_top]
        exact le_top
      refine le_of_eq ?_
      nth_rw 2 [← ENNReal.rpow_one ((f + g) a)]
      rw [← ENNReal.rpow_add _ _ h_zero h_top, add_sub_cancel]
    _ = (∫⁻ a : α, f a * (f + g) a ^ (p - 1) ∂μ) + ∫⁻ a : α, g a * (f + g) a ^ (p - 1) ∂μ := by
      have h_add_m : AEMeasurable (fun a : α => (f + g) a ^ (p - 1 : ℝ)) μ :=
        (hf.add hg).pow_const _
      have h_add_apply :
        (∫⁻ a : α, (f + g) a * (f + g) a ^ (p - 1) ∂μ) =
          ∫⁻ a : α, (f a + g a) * (f + g) a ^ (p - 1) ∂μ :=
        rfl
      simp_rw [h_add_apply, add_mul]
      rw [lintegral_add_left' (hf.fun_mul h_add_m)]
    _ ≤
        ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) *
          (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q) := by
      rw [add_mul]
      gcongr
      · exact manuscript_lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hf (hf.add hg)
      · exact manuscript_lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hg (hf.add hg)

theorem manuscript_lintegral_Lp_add_le_aux {p q : ℝ} (hpq : p.HolderConjugate q) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (h_add_zero : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ 0)
    (h_add_top : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by
  have h0_rpow : (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≠ 0 := by
    simp [h_add_zero, h_add_top, -Pi.add_apply]
  suffices h :
    1 ≤
      (∫⁻ a : α, (f + g) a ^ p ∂μ) ^ (-(1 / p)) *
        ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a : α, g a ^ p ∂μ) ^ (1 / p)) by
    rwa [← ENNReal.mul_le_mul_iff_right h0_rpow (by finiteness),
      ← mul_assoc, ← rpow_add _ _ h_add_zero h_add_top, ←
      sub_eq_add_neg, _root_.sub_self, rpow_zero, one_mul, mul_one] at h
  have h :
    (∫⁻ a : α, (f + g) a ^ p ∂μ) ≤
      ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a : α, g a ^ p ∂μ) ^ (1 / p)) *
        (∫⁻ a : α, (f + g) a ^ p ∂μ) ^ (1 / q) :=
    manuscript_lintegral_rpow_add_le_add_eLpNorm_mul_lintegral_rpow_add hpq hf hg
  have h_one_div_q : 1 / q = 1 - 1 / p := by
    nth_rw 2 [← hpq.inv_add_inv_eq_one]
    ring
  simp_rw [h_one_div_q, sub_eq_add_neg 1 (1 / p), ENNReal.rpow_add _ _ h_add_zero h_add_top,
    rpow_one] at h
  conv_rhs at h => enter [2]; rw [mul_comm]
  conv_lhs at h => rw [← one_mul (∫⁻ a : α, (f + g) a ^ p ∂μ)]
  rwa [← mul_assoc, ENNReal.mul_le_mul_iff_left h_add_zero h_add_top, mul_comm] at h

/-- **Minkowski's inequality for functions** `α → ℝ≥0∞`: the `ℒp` seminorm of the sum of two
functions is bounded by the sum of their `ℒp` seminorms. -/
theorem manuscript_lintegral_Lp_add_le {p : ℝ} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hp1 : 1 ≤ p) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  obtain hf_top | hf_top := eq_top_or_lt_top (∫⁻ a, f a ^ p ∂μ)
  · simp [hf_top, hp_pos]
  obtain hg_top | hg_top := eq_top_or_lt_top (∫⁻ a, g a ^ p ∂μ)
  · simp [hg_top, hp_pos]
  by_cases h1 : p = 1
  · refine le_of_eq ?_
    simp_rw [h1, one_div_one, ENNReal.rpow_one]
    exact lintegral_add_left' hf _
  have hp1_lt : 1 < p := by
    refine lt_of_le_of_ne hp1 ?_
    symm
    exact h1
  have hpq := Real.HolderConjugate.conjExponent hp1_lt
  by_cases h0 : (∫⁻ a, (f + g) a ^ p ∂μ) = 0
  · rw [h0, @ENNReal.zero_rpow_of_pos (1 / p) (by simp [lt_of_lt_of_le zero_lt_one hp1])]
    exact zero_le
  exact manuscript_lintegral_Lp_add_le_aux hpq hf hg h0
    (manuscript_lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top hf hf_top hg_top hp1).ne


end Asakura
