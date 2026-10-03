import Chapter8OUStationary
import Chapter4BrownianSystem

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000

/-- The scalar Einstein exercise, starting from the actual Ito solution.
Its transition Gaussian, stationary convolution, and physical variance
condition are conclusions of one theorem. -/
theorem scalar_einstein_exercise {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (μ k σ β x : ℝ) (hμ : 0<μ) (hk : 0<k) (hβ : 0<β) :
    ∃ N : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => σ*Real.exp ((μ*k)*z.2)) N ∧
      (∀ᵐ w ∂P,∀ R : ℝ,0≤R →
        Real.exp (-(μ*k)*R)*(x+N (realTimeClamp R) w)=x-
          (μ*k)*(∫ r in 0..R,Real.exp (-(μ*k)*r)*(x+N (realTimeClamp r) w))+
            σ*B.W 0 (realTimeClamp R) w) ∧
      (∀ (R : ℝ) (hR : 0≤R),
        HasLaw (fun w => Real.exp (-(μ*k)*R)*(x+N (realTimeClamp R) w))
          (ouKernel (μ*k) σ (mul_pos hμ hk) ⟨R,hR⟩ x) P) ∧
      (∀ t : ℝ≥0,
        (gaussianReal 0 (ouStationaryVariance (μ*k) σ (mul_pos hμ hk))).map
          (fun y => Real.exp (-(μ*k)*(t:ℝ))*y) ∗
          gaussianReal 0 (ouVariance (μ*k) σ (mul_pos hμ hk) t)=
            gaussianReal 0 (ouStationaryVariance (μ*k) σ (mul_pos hμ hk))) ∧
      (σ^2/(2*μ*k)=(β*k)⁻¹ ↔ σ^2=2*β⁻¹*μ) := by
  obtain ⟨N,hN,hNI,he,hl⟩ := ou_solution_and_transition_law P (T := ⊤) (by simp)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    (fun w r hr _ => B.diagonal_clock 0 w r hr) (μ*k) σ x (mul_pos hμ hk)
  refine ⟨N,hN,hNI,?_,?_,ou_stationary_gaussian (μ*k) σ (mul_pos hμ hk),
    scalar_einstein_variance_iff μ k σ β hμ hk hβ⟩
  · filter_upwards [he] with w hw
    intro R hR
    exact hw R hR (EReal.coe_lt_top R)
  · intro R hR
    exact hl R hR (EReal.coe_lt_top R)

end Asakura.Chapter8
