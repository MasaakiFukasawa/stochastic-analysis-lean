import Chapter11InvestmentIdentification
import Chapter11MertonConstructed

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Merton's verification applies to every solution of the investment SDE,
 rather than only to a separately constructed exponential process. -/
theorem investment_solution_merton_verified {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hm : Measurable π)
    (R : ℝ) (hR : 0<R)
    (hp : ∀ d,0<d → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => π (z.1,z.2.val)))
    (K x r μ σ γ : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K)
    (hx : 0<x) (hσ : σ≠0) (hγ : 0<γ) (hγ1 : γ≠1)
    (X M : HalfClosedTime → Ω → ℝ)
    (hXa : ∀ t,t<⊤ → Measurable[B.F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (hM : LocalMProcessWitness P B.F M)
    (hMI : ItoCovarianceFormula P B.F (B.W 0) (fun z => X (realTimeClamp z.2) z.1*(σ*π z)) M)
    (he : ∀ᵐ w ∂P,∀ t∈Icc 0 R,X (realTimeClamp t) w=x+
      (∫ s in 0..t,X (realTimeClamp s) w*(r+π (w,s)*(μ-r)))+M (realTimeClamp t) w) :
    Integrable (fun w => (X (realTimeClamp R) w)^(1-γ)/(1-γ)) P ∧
      (∫ w,(X (realTimeClamp R) w)^(1-γ)/(1-γ) ∂P)≤mertonValue r μ σ γ R 0 x ∧
      ((∀ z,π z=(μ-r)/(γ*σ^2)) →
        (∫ w,(X (realTimeClamp R) w)^(1-γ)/(1-γ) ∂P)=mertonValue r μ σ γ R 0 x) := by
  obtain ⟨V,N,L,hN,hL,hNI,hLI,hpos,hVe,hSDE⟩ := investment_wealth_constructed P B π hm hp K x r μ σ R hK hb hx hR
  have hform := investment_solution_identified P B π hm R hR (hp R hR) K x r μ σ hK hb
    X M N hXa hXc hM hMI hN hNI he
  have hEq : X (realTimeClamp R)=ᵐ[P] V (realTimeClamp R) := by
    filter_upwards [hform R ⟨hR.le,le_rfl⟩] with w hw
    exact hw.trans (hVe w R ⟨hR.le,le_rfl⟩).symm
  have hu : (fun w => (X (realTimeClamp R) w)^(1-γ)/(1-γ))=ᵐ[P]
      fun w => (V (realTimeClamp R) w)^(1-γ)/(1-γ) := hEq.fun_comp (fun z => z^(1-γ)/(1-γ))
  have hv := merton_actual_wealth_verified P B π hm hp K x r μ σ γ R hK hb hx hσ hγ hγ1 hR N V hN hNI hVe
  exact ⟨hv.1.congr hu.symm,by rw [integral_congr_ae hu];exact hv.2.1,
    fun hopt => (integral_congr_ae hu).trans (hv.2.2 hopt)⟩

end Asakura.Chapter11
