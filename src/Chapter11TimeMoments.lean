import Chapter11WealthMoments
import Chapter5ConditionalProcessEnergy

open MeasureTheory Set Filter
namespace Asakura.Chapter11
set_option maxHeartbeats 1500000

/-- Uniform bounds on the real moments give precisely the sample-time
integrability used by the Merton verification, including negative powers. -/
theorem uniform_moments_time_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V : Ω × ℝ → ℝ)
    (hV : Measurable V) (hpos : ∀ z,0<V z) (q T D : ℝ)
    (hi : ∀ t∈Icc 0 T,Integrable (fun w => (V (w,t))^q) P)
    (hb : ∀ t∈Icc 0 T,(∫ w,(V (w,t))^q ∂P)≤D) :
    Integrable (fun z => (V z)^q) (P.prod (volume.restrict (Icc 0 T))) := by
  apply (integrable_prod_iff' (hV.pow_const q).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hi t ht
  · have hm := ((hV.pow_const q).norm.stronglyMeasurable.integral_prod_left' (μ := P))
    apply (integrable_const D).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have he : (fun w => ‖(V (w,t))^q‖)=(fun w => (V (w,t))^q) := by
      funext w
      exact Real.norm_of_nonneg (Real.rpow_pos_of_pos (hpos _) q).le
    rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun w => (Real.rpow_pos_of_pos (hpos _) q).le))]
    exact hb t ht

/-- A bounded investment ratio controls the drift uniformly on a finite
horizon, without any continuity assumption on the strategy. -/
theorem bounded_strategy_drift (π : Ω × ℝ → ℝ) (K r μ T t : ℝ)
    (hK : 0≤K) (hb : ∀ z,|π z|≤K) (ht : t∈Icc 0 T) (w : Ω) :
    |∫ s in 0..t,r+π (w,s)*(μ-r)|≤(|r|+K*|μ-r|)*T := by
  have hd s : |r+π (w,s)*(μ-r)|≤|r|+K*|μ-r| :=
    (abs_add_le _ _).trans (by rw [abs_mul];gcongr;exact hb _)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=t)
    (fun s _ => show ‖r+π (w,s)*(μ-r)‖≤|r|+K*|μ-r| by simpa only [Real.norm_eq_abs] using hd s)
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left ht.2 (add_nonneg (abs_nonneg _) (mul_nonneg hK (abs_nonneg _))))

end Asakura.Chapter11
