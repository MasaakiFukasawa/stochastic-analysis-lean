import Chapter11ConstantIntegral
import Chapter4FinitePathLift
import Chapter6BoundedGirsanovData

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The density printed in the Black--Scholes proof is the density of the
constructed equivalent measure, not merely an abstract existence assertion. -/
theorem black_scholes_explicit_density {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (θ R : ℝ) (hR : 0≤R) :
    ∃ (Q : Measure Ω) (hQ : IsProbabilityMeasure Q),
      Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp (-θ*B.W 0 (realTimeClamp R) w-θ^2*R/2))) ∧
      (∫ w,Real.exp (-θ*B.W 0 (realTimeClamp R) w-θ^2*R/2) ∂P)=1 ∧
      (∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w) ∧
      ∃ BQ : BrownianSystem Q 1,BQ.F=B.F ∧
        ∀ t,0≤t → BQ.W 0 (realTimeClamp t)=ᵐ[Q]
          fun w => B.W 0 (realTimeClamp t) w+θ*min R t := by
  obtain ⟨N,C,hN,hNI,hC,hCe,Q,hQ,hQe,hmean,_,_,ha,BQ,hF,he⟩ :=
    bounded_girsanov_density_data P B (fun _ _ => -θ) (fun _ => measurable_const)
      (fun _ _ _ => measurable_const) |θ| (abs_nonneg _) (fun _ _ => by simp) R hR
  have hn := constant_ito_integral_unique P (by simp) B.F B.mono B.le B.null
    (B.W 0) (N 0) (B.martingale 0) (hN 0) (-θ) (hNI 0)
  have hd : (fun w => Real.exp ((∑ i,N i (realTimeClamp R) w)-C (realTimeClamp R) w/2))=ᵐ[P]
      fun w => Real.exp (-θ*B.W 0 (realTimeClamp R) w-θ^2*R/2) := by
    filter_upwards [hn,hCe R hR] with w hw hc
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,hc,hw _ (real_time_below R hR (EReal.coe_lt_top R)),
      neg_sq,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    congr 1
    ring
  refine ⟨Q,hQ,?_,(integral_congr_ae hd).symm.trans hmean,ha,BQ,hF,?_⟩
  · rw [hQe]
    exact withDensity_congr_ae (hd.mono fun w hw => congrArg ENNReal.ofReal hw)
  · intro t ht
    filter_upwards [he 0 t ht] with w hw
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_neg,sub_neg_eq_add,mul_comm] using hw

end Asakura.Chapter11
