import Chapter10KyleEquilibriumVariance
import Chapter10KyleConditionalScaling

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000

/-- Once the actual filter equals price, its deterministic conditional
variance is also the unconditional squared error used in the terminal and
admissibility estimates. -/
theorem kyle_actual_error_second_moment {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : MeasurableSpace Ω) (hle : H≤m) (V a p : Ω → ℝ) (S : ℝ)
    (hap : a=ᵐ[P] p)
    (hvar : P[(fun w => (V w-a w)^2)|H]=ᵐ[P] (fun _ => S)) :
    (∫ w,(V w-p w)^2 ∂P)=S := by
  letI : MeasurableSpace Ω := m
  calc
    _ = ∫ w,(V w-a w)^2 ∂P := integral_congr_ae (hap.mono (fun w hw => by dsimp only; rw [hw]))
    _ = ∫ w,P[(fun w => (V w-a w)^2)|H] w ∂P := (integral_condExp hle).symm
    _ = ∫ _ : Ω,S ∂P := integral_congr_ae hvar
    _ = S := by simp

end Asakura.Chapter10
