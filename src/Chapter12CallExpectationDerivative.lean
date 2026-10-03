import Chapter12CallParameterDerivative

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- A call's corner causes no additional derivative term when the
underlying variable has no atom at the strike. Local random Lipschitz
bounds justify the exchange with expectation. -/
theorem call_expectation_parameter_derivative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℝ → Ω → ℝ) (dA : Ω → ℝ) (θ K : ℝ) (s : Set ℝ) (hs : s ∈ 𝓝 θ)
    (hAm : ∀ a, Measurable (A a)) (hdAm : Measurable dA)
    (hAi : Integrable (A θ) P) (bound : Ω → ℝ) (hbi : Integrable bound P)
    (hlip : ∀ᵐ w ∂P, LipschitzOnWith (Real.nnabs (bound w)) (fun a => A a w) s)
    (hd : ∀ᵐ w ∂P, HasDerivAt (fun a => A a w) (dA w) θ)
    (hno : P {w | A θ w = K} = 0) :
    HasDerivAt (fun a => ∫ w,max (A a w-K) 0 ∂P)
      (∫ w,(if K < A θ w then 1 else 0)*dA w ∂P) θ := by
  have hneq : ∀ᵐ w ∂P, A θ w ≠ K := by
    rw [ae_iff]
    simpa only [not_not] using hno
  have hmeas : Measurable (fun w => (if K < A θ w then (1:ℝ) else 0)*dA w) := by
    exact (measurable_const.ite (measurableSet_lt measurable_const (hAm θ)) measurable_const).mul hdAm
  have hcallLip : ∀ᵐ w ∂P, LipschitzOnWith (Real.nnabs (bound w))
      (fun a => max (A a w-K) 0) s := by
    filter_upwards [hlip] with w hw
    simpa only [one_mul,Function.comp_def] using (call_payoff_lipschitz K).comp_lipschitzOnWith hw
  have hcallDiff : ∀ᵐ w ∂P, HasDerivAt (fun a => max (A a w-K) 0)
      ((if K < A θ w then 1 else 0)*dA w) θ := by
    filter_upwards [hd,hneq] with w hw hk
    exact call_parameter_derivative (fun a => A a w) (dA w) θ K hw hk
  exact (hasDerivAt_integral_of_dominated_loc_of_lip (μ := P) hs
    (Eventually.of_forall (fun a => ((hAm a).sub_const K |>.max measurable_const).aestronglyMeasurable))
    ((hAi.sub (integrable_const K)).pos_part) hmeas.aestronglyMeasurable hcallLip hbi hcallDiff).2

end Asakura.Chapter12
