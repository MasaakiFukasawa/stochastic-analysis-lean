import Chapter8DeterministicItoMoment

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The Euclidean second moment is the integral of the sum of squared
coefficient entries, also for rectangular and degenerate noise matrices. -/
theorem deterministic_vector_ito_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d p : ℕ} (B : BrownianSystem P d)
    (G : Fin p → Fin d → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    (R : ℝ) (hR : 0≤R) :
    (∀ i,MemLp (fun w => ∑ j,N i j (realTimeClamp R) w) 2 P) ∧
      (∫ w,‖WithLp.toLp 2 (fun i => ∑ j,N i j (realTimeClamp R) w)‖^2 ∂P)=
        ∫ r in 0..R,∑ i,∑ j,(G i j r)^2 := by
  classical
  have hh i := deterministic_ito_projection_second_moment P B G hG N hN hNI (Pi.single i 1) R hR
  simp only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hh
  refine ⟨fun i => (hh i).1,?_⟩
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finset_sum _ (fun i _ => (hh i).1.integrable_sq)]
  simp_rw [fun i => (hh i).2]
  rw [intervalIntegral.integral_finset_sum]
  intro i _
  exact (continuous_finsetSum _ (fun j _ => (hG i j).pow 2)).intervalIntegrable _ _
end Asakura.Chapter8
