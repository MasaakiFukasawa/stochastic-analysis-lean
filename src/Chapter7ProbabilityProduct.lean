import Chapter7MeanSquareProbability
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The product step in the drift remainder: convergence in probability
can be multiplied by a family with uniformly bounded first absolute moments.
No independence is required. -/
theorem probability_product_bounded_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ℕ → Ω → ℝ)
    (hX : TendstoInMeasure P X atTop (fun _ => 0))
    (hi : ∀ n,Integrable (fun w => |Y n w|) P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n,(∫ w,|Y n w| ∂P) ≤ C) :
    TendstoInMeasure P (fun n w => X n w*Y n w) atTop (fun _ => 0) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  simp only [Real.dist_eq,sub_zero]
  have hr : Tendsto (fun n => P.real {w | ε ≤ |X n w*Y n w|}) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun n => ha.trans_le measureReal_nonneg)
    · intro δ hδ
      let R := 1+2*C/δ
      have hR : 0 < R := by dsimp [R]; positivity
      have hCR : C/R < δ/2 := by
        apply (div_lt_iff₀ hR).mpr
        dsimp [R]
        field_simp
        nlinarith
      have hp := tendstoInMeasure_iff_dist.mp hX (ε/R) (div_pos hε hR)
      have hpR := (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp hp
      simp only [Real.dist_eq,sub_zero,Function.comp_def,ENNReal.toReal_zero] at hpR
      filter_upwards [hpR.eventually (gt_mem_nhds (half_pos hδ))] with n hn
      have htail : P.real {w | R ≤ |Y n w|} ≤ C/R := by
        apply (le_div_iff₀ hR).mpr
        have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all P fun w => abs_nonneg (Y n w)) (hi n) R
        nlinarith [hb n]
      have hsub : {w | ε ≤ |X n w*Y n w|} ⊆
          {w | ε/R ≤ |X n w|} ∪ {w | R ≤ |Y n w|} := by
        intro w hw
        by_contra hn
        have hx : |X n w| < ε/R := lt_of_not_ge (fun h => hn (Or.inl h))
        have hy : |Y n w| < R := lt_of_not_ge (fun h => hn (Or.inr h))
        have hx' := (lt_div_iff₀ hR).mp hx
        have hxy := mul_le_mul_of_nonneg_left hy.le (abs_nonneg (X n w))
        change ε ≤ |X n w*Y n w| at hw
        rw [abs_mul] at hw
        linarith
      have hbound := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le _ _)
      change P.real {w | ε/R ≤ |X n w|} < δ/2 at hn
      linarith
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_zero] using hh

end Asakura.Chapter7
