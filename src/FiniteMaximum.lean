import Appendix
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace Asakura

/-- C.2: the random maximum on a finite edge set. -/
noncomputable def finiteNormMax {I Ω : Type*} [Fintype I] (F : I → Ω → ℝ) (ω : Ω) : ℝ :=
  ⨆ i, ‖F i ω‖

theorem finiteNormMax_measurable {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    (F : I → Ω → ℝ) (hF : ∀ i, Measurable (F i)) : Measurable (finiteNormMax F) :=
  Measurable.iSup (fun i => (hF i).norm)

theorem finiteNormMax_nonneg {I Ω : Type*} [Fintype I] [Nonempty I]
    (F : I → Ω → ℝ) (ω : Ω) : 0 ≤ finiteNormMax F ω := by
  obtain ⟨i, hi⟩ := Finite.ciSup_mem (fun i => ‖F i ω‖)
  change 0 ≤ ⨆ i, ‖F i ω‖
  rw [← hi]
  exact norm_nonneg _

theorem le_finiteNormMax {I Ω : Type*} [Fintype I]
    (F : I → Ω → ℝ) (i : I) (ω : Ω) : ‖F i ω‖ ≤ finiteNormMax F ω :=
  le_ciSup (Set.finite_range (fun j => ‖F j ω‖)).bddAbove i

/-- C.2: the p-th moment of a finite maximum is bounded by the sum of moments. -/
theorem finite_maximum_lp_power {I Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] (μ : Measure Ω) (p : ℝ≥0) (hp : p ≠ 0)
    (F : I → Ω → ℝ) (hF : ∀ i, Measurable (F i)) :
    (eLpNorm (finiteNormMax F) p μ)^(p : ℝ) ≤
      ∑ i : I, (eLpNorm (F i) p μ)^(p : ℝ) := by
  rw [eLpNorm_nnreal_pow_eq_lintegral hp (finiteNormMax_measurable F hF).aestronglyMeasurable]
  simp_rw [eLpNorm_nnreal_pow_eq_lintegral hp (hF _).aestronglyMeasurable]
  rw [← lintegral_finsetSum _ (fun i _ => (hF i).enorm.pow_const (p : ℝ))]
  apply lintegral_mono
  intro ω
  obtain ⟨i, hi⟩ := Finite.ciSup_mem (fun i => ‖F i ω‖)
  have heq : finiteNormMax F ω = ‖F i ω‖ := hi.symm
  change ‖finiteNormMax F ω‖ₑ ^ (p : ℝ) ≤ ∑ j : I, ‖F j ω‖ₑ ^ (p : ℝ)
  rw [heq, enorm_norm]
  exact Finset.single_le_sum (fun j _ => show (0 : ℝ≥0∞) ≤ ‖F j ω‖ₑ ^ (p : ℝ) from bot_le) (Finset.mem_univ i)

/-- C.2: a common Lp bound on every edge gives the cardinality-to-the-1/p bound. -/
theorem finite_maximum_lp_bound {I Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] (μ : Measure Ω) (p : ℝ≥0) (hp : p ≠ 0)
    (F : I → Ω → ℝ) (hF : ∀ i, Measurable (F i)) (C : ℝ≥0∞)
    (hbound : ∀ i, eLpNorm (F i) p μ ≤ C) :
    eLpNorm (finiteNormMax F) p μ ≤ (Fintype.card I : ℝ≥0∞)^(1/(p:ℝ)) * C := by
  have hp0 : 0 < (p : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hp)
  have hsum : (∑ i : I, (eLpNorm (F i) p μ)^(p:ℝ)) ≤
      (Fintype.card I : ℝ≥0∞) * C^(p:ℝ) := by
    calc
      _ ≤ ∑ i : I, C^(p:ℝ) := Finset.sum_le_sum
        (fun i _ => ENNReal.rpow_le_rpow (hbound i) hp0.le)
      _ = _ := by simp
  have h := ENNReal.rpow_le_rpow ((finite_maximum_lp_power μ p hp F hF).trans hsum)
    (by positivity : (0:ℝ) ≤ 1/(p:ℝ))
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1/(p:ℝ)),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h
  exact h
end Asakura
