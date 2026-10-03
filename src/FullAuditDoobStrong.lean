import FullAuditDoobLayercake
import FullAuditLpComplete

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Division by the truncated norm, treating the zero case separately. -/
theorem ennreal_cancel_doob_power (x b : ENNReal) (p : ℝ) (hp : 1 < p)
    (hx : x ≠ ∞) (h : x ^ p ≤ b * x ^ (p-1)) : x ≤ b := by
  by_cases h0 : x = 0
  · simp [h0]
  have hpow0 : x ^ (p-1) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr h0) hx).ne'
  have hpowtop : x ^ (p-1) ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero h0 hx
  have he : x ^ p = x * x ^ (p-1) := by
    calc
      _ = x ^ (1+(p-1)) := by congr 1; ring
      _ = x ^ (1:ℝ) * x ^ (p-1) := ENNReal.rpow_add _ _ h0 hx
      _ = _ := by rw [ENNReal.rpow_one]
  rw [he] at h
  exact (ENNReal.mul_le_mul_iff_left hpow0 hpowtop).mp h

/-- The layer-cake and Holder step for a finite truncated pth moment. -/
theorem doob_strong_finite_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y S : Ω → ℝ) (hY : Measurable Y) (hS : Measurable S)
    (hpos : ∀ ω, 0 ≤ S ω) (p : ℝ) (hp : 1 < p)
    (hfinite : (∫⁻ ω, (ENNReal.ofReal (S ω)) ^ p ∂μ) ≠ ∞)
    (htail : ∀ t > 0, ENNReal.ofReal t * μ {ω | t ≤ S ω} ≤
      (μ.withDensity (fun ω => ENNReal.ofReal (Y ω))) {ω | t ≤ S ω}) :
    (∫⁻ ω, (ENNReal.ofReal (S ω)) ^ p ∂μ) ^ (1/p) ≤
      ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, (ENNReal.ofReal (Y ω)) ^ p ∂μ) ^ (1/p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.HolderConjugate (p/(p-1)) := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hl := doob_layercake_two_measures μ (μ.withDensity (fun ω => ENNReal.ofReal (Y ω)))
    S hS hpos p hp htail
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (hpos _) hp0.le] at hl
  have hpow : ∀ ω, ENNReal.ofReal (S ω ^ (p-1)) = ENNReal.ofReal (S ω) ^ (p-1) :=
    fun ω => (ENNReal.ofReal_rpow_of_nonneg (hpos ω) (sub_nonneg.mpr hp.le)).symm
  simp_rw [hpow] at hl
  rw [lintegral_withDensity_eq_lintegral_mul μ hY.ennreal_ofReal
    (hS.ennreal_ofReal.pow_const _)] at hl
  have hh := Asakura.manuscript_lintegral_mul_le_Lp_mul_Lq μ hpq
    hY.ennreal_ofReal.aemeasurable (hS.ennreal_ofReal.pow_const (p-1)).aemeasurable
  simp_rw [← ENNReal.rpow_mul, hpq.sub_one_mul_conj] at hh
  let A := ∫⁻ ω, ENNReal.ofReal (S ω) ^ p ∂μ
  let B := ∫⁻ ω, ENNReal.ofReal (Y ω) ^ p ∂μ
  let x := A ^ (1/p)
  have hx : x ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hp0.le) hfinite
  have hxp : x ^ p = A := by
    dsimp [x]
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have hxq : x ^ (p-1) = A ^ (1/(p/(p-1))) := by
    dsimp [x]
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  apply ennreal_cancel_doob_power x _ p hp hx
  rw [hxp,hxq]
  calc
    A ≤ ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, ENNReal.ofReal (Y ω) * ENNReal.ofReal (S ω) ^ (p-1) ∂μ) := hl
    _ ≤ ENNReal.ofReal (p/(p-1)) * (B ^ (1/p) * A ^ (1/(p/(p-1)))) := by
      gcongr 1
      exact hh
    _ = _ := by rw [mul_assoc]

/-- Remove the cutoff by the manuscript's monotone-convergence argument. -/
theorem doob_strong_written {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y S : Ω → ℝ)
    (hY : Measurable Y) (hS : Measurable S) (hpos : ∀ ω, 0 ≤ S ω)
    (p : ℝ) (hp : 1 < p)
    (htail : ∀ t > 0, ENNReal.ofReal t * μ {ω | t ≤ S ω} ≤
      (μ.withDensity (fun ω => ENNReal.ofReal (Y ω))) {ω | t ≤ S ω}) :
    (∫⁻ ω, (ENNReal.ofReal (S ω)) ^ p ∂μ) ^ (1/p) ≤
      ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, (ENNReal.ofReal (Y ω)) ^ p ∂μ) ^ (1/p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let T : ℕ → Ω → ℝ := fun n ω => min (S ω) (n:ℝ)
  let f : ℕ → Ω → ENNReal := fun n ω => ENNReal.ofReal (T n ω) ^ p
  let b := ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, ENNReal.ofReal (Y ω) ^ p ∂μ) ^ (1/p)
  have hT : ∀ n, Measurable (T n) := fun n => hS.min measurable_const
  have hTpos : ∀ n ω, 0 ≤ T n ω := fun n ω => le_min (hpos ω) (Nat.cast_nonneg n)
  have hf : ∀ n, Measurable (f n) := fun n => (hT n).ennreal_ofReal.pow_const p
  have hmono : Monotone f := by
    intro n k hnk ω
    apply ENNReal.rpow_le_rpow _ hp0.le
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hnk))
  have hsup : ∀ ω, (⨆ n, f n ω) = ENNReal.ofReal (S ω) ^ p := by
    intro ω
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (min_le_left _ _)) hp0.le
    · obtain ⟨n, hn⟩ := exists_nat_ge (S ω)
      exact le_iSup_of_le n (by change _ ≤ ENNReal.ofReal (min (S ω) (n:ℝ)) ^ p; rw [min_eq_left hn])
  have hbound : ∀ n, (∫⁻ ω, f n ω ∂μ) ≤ b ^ p := by
    intro n
    have hfin : (∫⁻ ω, f n ω ∂μ) ≠ ∞ := by
      apply ne_top_of_le_ne_top (show (ENNReal.ofReal (n:ℝ)) ^ p ≠ ∞ from
        ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
      calc
        _ ≤ ∫⁻ ω, ENNReal.ofReal (n:ℝ) ^ p ∂μ := lintegral_mono fun ω =>
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (min_le_right _ _)) hp0.le
        _ = _ := by simp
    have ht : ∀ t > 0, ENNReal.ofReal t * μ {ω | t ≤ T n ω} ≤
        (μ.withDensity (fun ω => ENNReal.ofReal (Y ω))) {ω | t ≤ T n ω} := by
      intro t ht
      by_cases htn : t ≤ (n:ℝ)
      · simpa only [T,le_min_iff,and_true,htn] using htail t ht
      · have he : {ω | t ≤ T n ω} = ∅ := by ext ω; simp [T,le_min_iff,htn]
        simp [he]
    have h := doob_strong_finite_moment μ Y (T n) hY (hT n) (hTpos n) p hp hfin ht
    have hh := ENNReal.rpow_le_rpow h hp0.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one] at hh
    exact hh
  have hall : (∫⁻ ω, ENNReal.ofReal (S ω) ^ p ∂μ) ≤ b ^ p := by
    simp_rw [← hsup]
    rw [Asakura.manuscript_monotone_convergence (μ := μ) hf hmono]
    exact iSup_le hbound
  have h := ENNReal.rpow_le_rpow hall (one_div_nonneg.mpr hp0.le)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h
  exact h

end Asakura.FullAudit
