import Chapter6LinearLikelihoodBrownian
import Chapter6LikelihoodErrorWritten

open MeasureTheory Set Filter Finset Matrix
open scoped Topology BigOperators NNReal ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- Construct the true-parameter probability measure and its Brownian
noise, then derive the estimation error using the actual Ito integrals. -/
theorem likelihood_error_constructed_measure {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (H N : Fin n → Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ k j t,Measurable[B.F t] (H k j t)) (hHc : ∀ k j w,Continuous (fun t => H k j t w))
    (hN : ∀ k j,LocalMProcessWitness P B.F (N k j))
    (hNI : ∀ k j,ItoCovarianceFormula P B.F (B.W j) (fun z => H k j (realTimeClamp z.2) z.1) (N k j))
    (K : ℝ) (hK : 0≤K) (hHb : ∀ k j t w,|H k j t w|≤K)
    (R : ℝ) (hR : 0<R) (θ : Fin n → ℝ) :
    let score := fun w k => ∑ j,N k j (realTimeClamp R) w
    let info : Ω → Matrix (Fin n) (Fin n) ℝ := fun w k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w
    ∃ (Q : Measure Ω) (hQp : IsProbabilityMeasure Q),
      Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp (quadraticLogLikelihood (info w) (score w) θ))) ∧
      ∃ (BQ : BrownianSystem Q d) (M : Fin n → Fin d → HalfClosedTime → Ω → ℝ),
        BQ.F=B.F ∧ (∀ k j,LocalMProcessWitness Q BQ.F (M k j)) ∧
        (∀ k j,ItoCovarianceFormula Q BQ.F (BQ.W j) (fun z => H k j (realTimeClamp z.2) z.1) (M k j)) ∧
        (∀ᵐ w ∂Q,score w=info w *ᵥ θ+(fun k => ∑ j,M k j (realTimeClamp R) w) ∧
          ((info w).PosDef → (info w)⁻¹ *ᵥ score w-θ=(info w)⁻¹ *ᵥ (fun k => ∑ j,M k j (realTimeClamp R) w))) := by
  obtain ⟨Q,hQp,density,hd,hd2,hQD,hQ,BQ,hF,hW⟩ := linear_likelihood_changed_brownian P B H N hHa hHc hN hNI K hK hHb R hR.le θ
  letI : IsProbabilityMeasure Q := hQp
  obtain ⟨M,hM,hMI,he⟩ := likelihood_error_written P Q B BQ hF density hd hQD hd2 H N hHa hHc hN hNI K hK hHb R hR θ hW
  exact ⟨Q,hQp,hQ,BQ,M,hF,hM,hMI,he⟩

end Asakura.Chapter6
