import Chapter11InvestmentIdentification
import Chapter11LogConstructed

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- The expected-log identity and bound for every solution of the actual
 investment SDE, using the noise constructed by the Ito integral. -/
theorem investment_solution_log_verified {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hm : Measurable π)
    (R : ℝ) (hR : 0<R)
    (hp : ∀ d,0<d → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => π (z.1,z.2.val)))
    (K x r μ σ : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K)
    (hx : 0<x) (hσ : σ≠0)
    (X M : HalfClosedTime → Ω → ℝ)
    (hXa : ∀ t,t<⊤ → Measurable[B.F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (hM : LocalMProcessWitness P B.F M)
    (hMI : ItoCovarianceFormula P B.F (B.W 0) (fun z => X (realTimeClamp z.2) z.1*(σ*π z)) M)
    (he : ∀ᵐ w ∂P,∀ t∈Icc 0 R,X (realTimeClamp t) w=x+
      (∫ s in 0..t,X (realTimeClamp s) w*(r+π (w,s)*(μ-r)))+M (realTimeClamp t) w) :
    Integrable (fun w => Real.log (X (realTimeClamp R) w)) P ∧
      (∫ w,Real.log (X (realTimeClamp R) w) ∂P)=Real.log x+(r+(μ-r)^2/(2*σ^2))*R-
        σ^2/2*(∫ w,(∫ t in Icc 0 R,(π (w,t)-(μ-r)/σ^2)^2) ∂P) ∧
      (∫ w,Real.log (X (realTimeClamp R) w) ∂P)≤Real.log x+(r+(μ-r)^2/(2*σ^2))*R ∧
      ((∀ z,π z=(μ-r)/σ^2) →
        (∫ w,Real.log (X (realTimeClamp R) w) ∂P)=Real.log x+(r+(μ-r)^2/(2*σ^2))*R) := by
  obtain ⟨N,hN,hNI,hVi,hVe,hVb,hVopt⟩ := actual_log_utility P B π hm hp K x r μ σ R hK hb hx hσ hR.le
  have hform := investment_solution_identified P B π hm R hR (hp R hR) K x r μ σ hK hb
    X M N hXa hXc hM hMI hN hNI he
  have hEq : X (realTimeClamp R)=ᵐ[P]
      terminalLogWealth (fun w t => π (w,t)) (N (realTimeClamp R)) x r μ σ R := by
    filter_upwards [hform R ⟨hR.le,le_rfl⟩] with w hw
    rw [hw,intervalIntegral.integral_of_le hR.le]
    simp only [terminalLogWealth,integral_Icc_eq_integral_Ioc]
  have hu := hEq.fun_comp Real.log
  exact ⟨hVi.congr hu.symm,(integral_congr_ae hu).trans hVe,
    (integral_congr_ae hu).le.trans hVb,
    fun hopt => (integral_congr_ae hu).trans (hVopt hopt)⟩

end Asakura.Chapter11
