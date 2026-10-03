import Chapter4OUKernelConstructed
import Chapter4BrownianSystem
import Chapter8BrownianForcingPath

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The vector OU solution is built from actual Ito integrals for an
arbitrary rectangular constant diffusion matrix, including the zero matrix. -/
theorem vector_ou_constructed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (σ : Fin d → Fin n → ℝ) :
    ∃ N : Fin d → Fin n → HalfClosedTime → Ω → ℝ,
      (∀ i j,LocalMProcessWitness P B.F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => σ i j*Real.exp z.2) (N i j)) ∧
      ∀ x : Fin d → ℝ,∀ᵐ w ∂P,∀ t≥0,∀ i,
        Real.exp (-t)*(x i+∑ j,N i j (realTimeClamp t) w)=x i-
          (∫ s in 0..t,Real.exp (-s)*(x i+∑ j,N i j (realTimeClamp s) w))+
          ∑ j,σ i j*B.W j (realTimeClamp t) w := by
  have hex i j := ou_sde_constructed P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null
    (B.W j) (B.C j j) (B.martingale j) (B.cov j j)
    (fun w r hr _ => B.diagonal_clock j w r hr) 0 (-1) (σ i j)
  choose N hN hNI he using hex
  refine ⟨N,hN,?_,?_⟩
  · intro i j
    simpa only [neg_neg,one_mul] using hNI i j
  intro x
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (he i))] with w hw
  intro t ht i
  have hc j : Continuous (fun s : ℝ => Real.exp (-s)*N i j (realTimeClamp s) w) := by
    apply Continuous.mul (by fun_prop)
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ((hN i j).path P B.F w _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have hsum : Real.exp (-t)*(∑ j,N i j (realTimeClamp t) w)=
      -(∫ s in 0..t,∑ j,Real.exp (-s)*N i j (realTimeClamp s) w)+
        ∑ j,σ i j*B.W j (realTimeClamp t) w := by
    have hh := congrArg (fun f : Fin n → ℝ => ∑ j,f j)
      (funext (fun j => hw i j t ht (EReal.coe_lt_top t)))
    simp only [neg_one_mul,zero_add,Finset.sum_add_distrib,Finset.sum_neg_distrib] at hh
    rw [←Finset.mul_sum] at hh
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hc j).intervalIntegrable 0 t)]
    exact hh
  have hi : (∫ s in 0..t,Real.exp (-s)*(x i+∑ j,N i j (realTimeClamp s) w))=
      x i*(∫ s in 0..t,Real.exp (-s))+(∫ s in 0..t,∑ j,Real.exp (-s)*N i j (realTimeClamp s) w) := by
    simp_rw [mul_add,Finset.mul_sum,mul_comm (Real.exp _) (x i)]
    rw [intervalIntegral.integral_add
      ((show Continuous (fun s : ℝ => Real.exp (-s)) by fun_prop).const_mul (x i) |>.intervalIntegrable 0 t)
      ((continuous_finset_sum _ (fun j _ => hc j)).intervalIntegrable 0 t),intervalIntegral.integral_const_mul]
  have hdet := exponential_weight_integral (-1) t
  simp only [neg_one_mul] at hdet
  rw [hi]
  nlinarith [congrArg (fun y : ℝ => x i*y) hdet]

end Asakura.Chapter8
