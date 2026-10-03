import Chapter11CommonIntegralLimit
import Chapter2ProbabilityErrorSum

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.Chapter2Complete
set_option maxHeartbeats 1500000

/-- Identify the same elementary trading gains from their martingale and
 variation limits. All limits are in probability, so no subsequence is chosen. -/
theorem gains_probability_identification {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure Q] (hQP : Q ≪ P)
    (Y V Z : ℕ → Ω → ℝ) (I L K : Ω → ℝ)
    (hZ : ∀ n,AEStronglyMeasurable (Z n) Q)
    (he : ∀ n, ∀ᵐ w ∂P,Z n w=Y n w+V n w)
    (hY : ∀ ε>0,Tendsto (fun n => P {w | ε≤|Y n w-I w|}) atTop (𝓝 0))
    (hV : ∀ ε>0,Tendsto (fun n => P {w | ε≤|V n w-L w|}) atTop (𝓝 0))
    (hK : ∀ ε>0,Tendsto (fun n => Q {w | ε≤|Z n w-K w|}) atTop (𝓝 0)) :
    (fun w => I w+L w)=ᵐ[Q] K := by
  have hp : TendstoInMeasure P Z atTop (fun w => I w+L w) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    simp only [Real.norm_eq_abs]
    apply probability_error_sum_limit P _ (fun n w => |Y n w-I w|) (fun n w => |V n w-L w|) 1 zero_lt_one _ hY hV ε hε
    intro n
    filter_upwards [he n] with w hw
    rw [hw,one_mul]
    calc
      |Y n w+V n w-(I w+L w)|=|(Y n w-I w)+(V n w-L w)| := by congr 1;ring
      _≤_ := abs_add_le _ _
  have hq : TendstoInMeasure Q Z atTop K := by
    rw [tendstoInMeasure_iff_norm]
    simpa only [Real.norm_eq_abs] using hK
  exact common_integral_limit P Q hQP Z _ K hZ hp hq

end Asakura.Chapter11
