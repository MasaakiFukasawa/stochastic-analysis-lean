import Chapter4DeterministicItoLaw
import Chapter4BrownianSystem

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The actual deterministic Brownian integral is integrable and centered. -/
theorem deterministic_noise_centered {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (B : BrownianSystem P n)
    (j : Fin n) (g : ℝ → ℝ) (hg : Continuous g)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W j) (fun z => g z.2) N)
    (r : ℝ) (hr : 0≤r) :
    Integrable (N (realTimeClamp r)) P ∧ (∫ w,N (realTimeClamp r) w ∂P)=0 := by
  have hl := deterministic_brownian_integral_law P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W j) (B.C j j) N (B.martingale j) (B.cov j j) hN
    (fun w s hs _ => B.diagonal_clock j w s hs) g hg hNI r hr (EReal.coe_lt_top _)
  refine ⟨hl.integrable ?_,?_⟩
  · exact (memLp_id_gaussianReal (1:ℝ≥0)).integrable (by norm_num)
  · rw [hl.integral_eq]
    exact integral_id_gaussianReal

end Asakura.Chapter10
