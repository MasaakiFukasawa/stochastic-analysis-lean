import Chapter12AsianInitialFunctions
import Chapter12AsianAverageMoments
import Chapter12CallExpectationDerivative
import Chapter12BrownianPathInputs
import Chapter12BrownianPathMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem asian_call_delta_expectation_exchange {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x r σ K : ℝ) (hx : 0 < x) (hσ : 0 < σ) :
    HasDerivAt (fun a => ∫ w,max (asianPathAverage a r T T.property σ (X w)-K) 0 ∂P)
      (∫ w,(if K < asianPathAverage x r T T.property σ (X w) then 1 else 0)*
        (asianPathAverage x r T T.property σ (X w)/x) ∂P) x := by
  have hi (a : ℝ) : Integrable (fun w => asianPathAverage a r T T.property σ (X w)) P :=
    memLp_one_iff_integrable.mp (asian_path_average_memLp P B hB hm hc T hT X hXm he a r σ 1 (by simp))
  have hno : P {w | asianPathAverage x r T T.property σ (X w) = K} = 0 :=
    brownian_arithmetic_average_no_atom P B hB x σ r T hx hσ hT X hXm
      (brownian_path_memLp P B hB hm hc T X hXm he 2 (by simp)) he K
  have hd := call_expectation_parameter_derivative P
    (fun a w => asianPathAverage a r T T.property σ (X w))
    (fun w => asianPathAverage 1 r T T.property σ (X w)) x K univ (Filter.univ_mem)
    (fun a => (asian_path_average_measurable a r T T.property σ).comp hXm)
    ((asian_path_average_measurable 1 r T T.property σ).comp hXm) (hi x) _ (hi 1)
    (ae_of_all P fun w => (asian_path_initial_lipschitz r T σ T.property (X w)).lipschitzOnWith)
    (ae_of_all P fun w => asian_path_initial_derivative x r T σ T.property (X w)) hno
  have hv (w : Ω) : asianPathAverage x r T T.property σ (X w)/x =
      asianPathAverage 1 r T T.property σ (X w) := by
    rw [asian_path_average_linear_initial]
    field_simp
  simpa only [hv] using hd

end Asakura.Chapter12
