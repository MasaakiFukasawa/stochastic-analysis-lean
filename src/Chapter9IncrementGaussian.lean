import Chapter9VectorIncrement
import Chapter8BrownianForcingPath

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem vector_ito_increment_projection_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d p : ℕ} (B : BrownianSystem P d)
    (G : Fin p → Fin d → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    (v : Fin p → ℝ) (R s : ℝ) (hR : 0≤R) (hs : s∈Icc 0 R) :
    HasLaw (fun w => ∑ i,v i*(Finset.sum Finset.univ (fun j : Fin d =>
      N i j (realTimeClamp R) w-N i j (realTimeClamp s) w)))
      (gaussianReal 0 ⟨∫ r in s..R,∑ j,(∑ i,v i*G i j r)^2,
        intervalIntegral.integral_nonneg_of_forall hs.2 (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))⟩) P := by
  let V := ∫ r in s..R,∑ j,(∑ i,v i*G i j r)^2
  have hm : Measurable (fun w => ∑ i,v i*(Finset.sum Finset.univ (fun j : Fin d =>
      N i j (realTimeClamp R) w-N i j (realTimeClamp s) w))) := by
    apply Finset.measurable_sum
    intro i _
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro j _
    exact (((hN i j).adapted P B.F _ (half_real_time_finite R)).mono (B.le _) le_rfl).sub
      (((hN i j).adapted P B.F _ (half_real_time_finite s)).mono (B.le _) le_rfl)
  apply (gaussian_independent_of_conditional_characteristic P (B.F (realTimeClamp s)) (B.le _)
    _ hm _ ?_).1
  intro u
  have hh := vector_ito_increment_characteristic P B G hG N hN hNI (fun i => u*v i) R s hR hs
  have he w : (∑ i,(u*v i)*(Finset.sum Finset.univ (fun j : Fin d =>
      N i j (realTimeClamp R) w-N i j (realTimeClamp s) w)))=
      u*(∑ i,v i*(Finset.sum Finset.univ (fun j : Fin d =>
      N i j (realTimeClamp R) w-N i j (realTimeClamp s) w))) := by
    simp only [Finset.mul_sum,mul_assoc]
  have hv : (∫ r in s..R,∑ j,(∑ i,(u*v i)*G i j r)^2)=u^2*V := by
    simp_rw [mul_assoc,←Finset.mul_sum,mul_pow,←Finset.mul_sum]
    exact intervalIntegral.integral_const_mul _ _
  simp_rw [he,hv,Complex.ofReal_mul] at hh
  convert hh using 1
  · funext w
    congr 1
    push_cast
    change -(V:ℂ)*(u:ℂ)^2/2 = -((u:ℂ)^2*(V:ℂ))/2
    ring
end Asakura.Chapter9
