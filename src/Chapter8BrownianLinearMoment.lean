import Chapter8DeterministicVectorMoment
import Chapter8SDEAdditiveEquation

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The Brownian forcing in the position formula has its usual finite
second moment even for a rectangular or rank-deficient matrix. -/
theorem brownian_linear_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (S : Fin d → Fin n → ℝ) (T : ℝ) (hT : 0≤T) :
    MemLp (fun w => WithLp.toLp 2 (fun i => ∑ j,S i j*B.W j (realTimeClamp T) w)) 2 P ∧
      (∫ w,‖WithLp.toLp 2 (fun i => ∑ j,S i j*B.W j (realTimeClamp T) w)‖^2 ∂P)=
        T*(∑ j,‖WithLp.toLp 2 (fun i => S i j)‖^2) := by
  let N := fun i j t w => S i j*B.W j t w
  have hN i j : LocalMProcessWitness P B.F (N i j) := (B.martingale j).smul P B.F (S i j)
  have hNI i j : ItoCovarianceFormula P B.F (B.W j) (fun _ => S i j) (N i j) :=
    constant_ito_integral P (by simp) B.F B.mono B.le B.null (B.W j) (B.martingale j) (S i j)
  obtain ⟨h2,he⟩ := deterministic_vector_ito_second_moment P B (fun i j _ => S i j)
    (fun _ _ => continuous_const) N hN hNI T hT
  have hv : MemLp (fun w => fun i => ∑ j,N i j (realTimeClamp T) w) 2 P := memLp_pi_iff.mpr h2
  refine ⟨?_,?_⟩
  · exact (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hv
  · rw [he,intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp]
    rw [Finset.sum_comm]
end Asakura.Chapter8
