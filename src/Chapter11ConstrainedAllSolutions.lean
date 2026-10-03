import Chapter11InvestmentIdentification
import Chapter11LogConstructed

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- The constrained exercise applies to every SDE solution; the clipped
 constant is optimal, with the actual noise proved to have mean zero. -/
theorem investment_solution_constrained_log_verified {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hm : Measurable π)
    (R : ℝ) (hR : 0<R)
    (hp : ∀ d,0<d → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => π (z.1,z.2.val)))
    (x r μ σ : ℝ) (hb : ∀ z,π z∈Icc 0 1)
    (hx : 0<x) (hσ : σ≠0)
    (X M : HalfClosedTime → Ω → ℝ)
    (hXa : ∀ t,t<⊤ → Measurable[B.F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (hM : LocalMProcessWitness P B.F M)
    (hMI : ItoCovarianceFormula P B.F (B.W 0) (fun z => X (realTimeClamp z.2) z.1*(σ*π z)) M)
    (he : ∀ᵐ w ∂P,∀ t∈Icc 0 R,X (realTimeClamp t) w=x+
      (∫ s in 0..t,X (realTimeClamp s) w*(r+π (w,s)*(μ-r)))+M (realTimeClamp t) w) :
    let p := min 1 (max 0 ((μ-r)/σ^2))
    let L := Real.log x+(r+p*(μ-r)-σ^2*p^2/2)*R
    (∫ w,Real.log (X (realTimeClamp R) w) ∂P)≤L ∧
      ((∀ z,π z=p) → (∫ w,Real.log (X (realTimeClamp R) w) ∂P)=L) := by
  have hbound z : |π z|≤1 := by rw [abs_of_nonneg (hb z).1];exact (hb z).2
  obtain ⟨N,C,hN,hNI,_,_,_,_,hmean⟩ := bounded_strategy_integral P B
    (fun z => σ*π z) (hm.const_mul σ) (fun d hd => (hp d hd).const_mul σ)
    (|σ| *1) (by positivity)
    (fun z => by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hbound z) (abs_nonneg σ))
  have hform := investment_solution_identified P B π hm R hR (hp R hR) 1 x r μ σ (by norm_num) hbound
    X M N hXa hXc hM hMI hN hNI he
  have hEq : X (realTimeClamp R)=ᵐ[P]
      terminalLogWealth (fun w t => π (w,t)) (N (realTimeClamp R)) x r μ σ R := by
    filter_upwards [hform R ⟨hR.le,le_rfl⟩] with w hw
    rw [hw,intervalIntegral.integral_of_le hR.le]
    simp only [terminalLogWealth,integral_Icc_eq_integral_Ioc]
  have hval := constrained_log_utility P (fun w t => π (w,t)) (N (realTimeClamp R)) x r μ σ R hx hσ hR.le hm
    (fun w t => hb (w,t)) (hmean R hR.le).1 (hmean R hR.le).2
  have hu := hEq.fun_comp Real.log
  exact ⟨(integral_congr_ae hu).le.trans hval.1,
    fun hopt => (integral_congr_ae hu).trans (hval.2 fun w t => hopt (w,t))⟩

end Asakura.Chapter11
