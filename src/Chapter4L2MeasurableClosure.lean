import Chapter4EulerEndpointLimit
import FullAuditConditionalLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- L2 limits retain a completed sigma algebra. Conditional-expectation
contraction gives the identification without invoking an a.s. subsequence. -/
theorem vector_L2_limit_measurable
    {Ω : Type*} {m : MeasurableSpace Ω} {dim : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (hnull : ∀ E,MeasurableSet[m] E → P E=0 → MeasurableSet[G] E)
    (Y : ℕ → Ω → Fin dim → ℝ) (X : Ω → Fin dim → ℝ)
    (hYm : ∀ n,Measurable[G] (Y n)) (hXm : Measurable[m] X)
    (hYi : ∀ n,MemLp (Y n) 2 P) (hXi : MemLp X 2 P)
    (ht : Tendsto (fun n => ∫ w,‖Y n w-X w‖^2 ∂P) atTop (𝓝 0)) : Measurable[G] X := by
  letI : MeasurableSpace Ω := m
  have hcoord : ∀ i,Measurable[G] (fun w => X w i) := by
    intro i
    have hi n : MemLp (fun w => Y n w i) 2 P := memLp_pi_iff.mp (hYi n) i
    have hxi : MemLp (fun w => X w i) 2 P := memLp_pi_iff.mp hXi i
    have htm : Tendsto (fun n => ∫ w,‖Y n w i-X w i‖^2 ∂P) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => integral_nonneg (fun w => sq_nonneg _)) _ ht
      intro n
      apply integral_mono ((hi n).sub hxi |>.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
        ((hYi n).sub hXi |>.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
      intro w
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (Y n w-X w) i) 2
    have hte : Tendsto (fun n => eLpNorm (fun w => Y n w i-X w i) 2 P) atTop (𝓝 0) := by
      have he n := path_eLpNorm_eq_sqrt_moment P (fun w => Y n w i-X w i) ((hi n).sub hxi)
      simp_rw [he]
      have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (Real.continuous_sqrt.continuousAt.tendsto.comp htm)
      simpa only [Real.sqrt_zero,ENNReal.ofReal_zero,Function.comp_def,Pi.sub_apply] using hh
    have hc n : (fun w => Y n w i)=ᵐ[P] P[(fun w => Y n w i) | G] := by
      have hmg : StronglyMeasurable[G] (fun w => Y n w i) := ((measurable_pi_apply i).comp (hYm n)).stronglyMeasurable
      have he := condExp_of_stronglyMeasurable hG hmg ((hi n).integrable (by norm_num : (1:ℝ≥0∞)≤2))
      exact Filter.Eventually.of_forall (fun w => (congrFun he w).symm)
    have hsame := Asakura.FullAudit.conditional_l2_limit_identity P hG
      (fun n w => Y n w i) (fun n w => Y n w i) (fun w => X w i) (fun w => X w i)
      hi hi hxi hxi hc hte hte
    exact Asakura.FullAudit.measurable_of_augmented_ae P hG hnull (fun w => X w i)
      P[(fun w => X w i) | G] ((measurable_pi_apply i).comp hXm)
      stronglyMeasurable_condExp.measurable hsame
  letI : MeasurableSpace Ω := G
  exact measurable_pi_iff.mpr hcoord

end Asakura.Chapter4
