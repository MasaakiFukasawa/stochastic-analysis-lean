import Chapter12AsianAverageMoments
import Chapter12CallExpectationDerivative
import Chapter12BrownianPathInputs

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The actual Asian call expectation may be differentiated in volatility.
The atomlessness, moments and common local Lipschitz envelope are all
discharged from the Brownian motion and the Black--Scholes path formula. -/
theorem asian_call_vega_expectation_exchange {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x r σ K : ℝ) (hx : 0 < x) (hσ : 0 < σ) :
    HasDerivAt (fun a => ∫ w,max (asianPathAverage x r T T.property a (X w)-K) 0 ∂P)
      (∫ w,(if K < asianPathAverage x r T T.property σ (X w) then 1 else 0)*
        asianPathVega x r T T.property σ (X w) ∂P) σ := by
  let L := |σ|+1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hs : Icc (-L) L ∈ 𝓝 σ := by
    apply Icc_mem_nhds
    · dsimp [L]
      linarith [neg_abs_le σ]
    · dsimp [L]
      linarith [le_abs_self σ]
  have hAi : Integrable (fun w => asianPathAverage x r T T.property σ (X w)) P :=
    memLp_one_iff_integrable.mp (asian_path_average_memLp P B hB hm hc T hT X hXm he x r σ 1 (by simp))
  have hbi : Integrable (fun w => asianVegaPathEnvelope x r T L (X w)) P :=
    memLp_one_iff_integrable.mp (asian_vega_envelope_memLp P B hB hm hc T X hXm he x r L 1 (by simp))
  have hX2 : MemLp X 2 P := by
    have hi := brownian_path_exponential_memLp P B hB hm hc T X hXm he 1 2 (by simp)
    apply hi.of_le hXm.aestronglyMeasurable
    apply ae_of_all
    intro w
    simp only [one_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    linarith [Real.add_one_le_exp ‖X w‖]
  have hno : P {w | asianPathAverage x r T T.property σ (X w) = K} = 0 :=
    brownian_arithmetic_average_no_atom P B hB x σ r T hx hσ hT X hXm hX2 he K
  exact call_expectation_parameter_derivative P
    (fun a w => asianPathAverage x r T T.property a (X w))
    (fun w => asianPathVega x r T T.property σ (X w)) σ K (Icc (-L) L) hs
    (fun a => (asian_path_average_measurable x r T T.property a).comp hXm)
    ((asian_path_vega_measurable x r T T.property σ).comp hXm) hAi _ hbi
    (ae_of_all P fun w => asian_path_volatility_lipschitz x r T L hT hL (X w))
    (ae_of_all P fun w => asian_path_volatility_derivative x r T T.property σ (X w)) hno

end Asakura.Chapter12
