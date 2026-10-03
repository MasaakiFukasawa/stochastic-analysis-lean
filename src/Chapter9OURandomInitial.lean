import Chapter9OUConstructed

open MeasureTheory Matrix
open scoped BigOperators
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Construct the explicit solution with a single null exceptional set
valid for all initial points. Hence substituting a random initial point
is legitimate; no uncountable intersection of full-measure sets is used. -/
theorem standard_ou_common_initial_construction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) :
    ∃ N : Fin d → Fin d → HalfClosedTime → Ω → ℝ,
      (∀ i j,LocalMProcessWitness P B.F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j)) ∧
      ∀ᵐ w ∂P,∀ x : Fin d → ℝ,∀ t≥0,∀ i,
        Real.exp (-t)*(x i+∑ j,N i j (realTimeClamp t) w)=x i-
          (∫ s in 0..t,Real.exp (-s)*(x i+∑ j,N i j (realTimeClamp s) w))+
          Real.sqrt 2*B.W i (realTimeClamp t) w := by
  obtain ⟨N,hN,hNI,hsol,_⟩ := standard_ou_constructed P B
  refine ⟨N,hN,hNI,?_⟩
  filter_upwards [hsol 0] with w hw
  intro x t ht i
  have hzero := hw t ht i
  simp only [Pi.zero_apply,zero_add,zero_sub] at hzero
  have hc : Continuous (fun s : ℝ => Real.exp (-s)*(∑ j,N i j (realTimeClamp s) w)) := by
    apply Continuous.mul (by fun_prop)
    apply continuous_finsetSum
    intro j _
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ((hN i j).path P B.F w _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  have hi : (∫ s in 0..t,Real.exp (-s)*(x i+∑ j,N i j (realTimeClamp s) w))=
      x i*(∫ s in 0..t,Real.exp (-s))+
        (∫ s in 0..t,Real.exp (-s)*(∑ j,N i j (realTimeClamp s) w)) := by
    simp_rw [mul_add,mul_comm (Real.exp _) (x i)]
    rw [intervalIntegral.integral_add
      ((show Continuous (fun s : ℝ => Real.exp (-s)) by fun_prop).const_mul (x i) |>.intervalIntegrable 0 t)
      (hc.intervalIntegrable 0 t),intervalIntegral.integral_const_mul]
  have hdet := exponential_weight_integral (-1) t
  simp only [neg_one_mul] at hdet
  rw [hi]
  nlinarith [congrArg (fun y : ℝ => x i*y) hdet]
end Asakura.Chapter9
