import EndToEndHJMAEModelComplete
import EndToEndParameterItoGlobal
open MeasureTheory Set Filter
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the parameterized Ito integrals and derive both global HJM
necessity and the original discounted bond-price exponential. -/
theorem hjm_constructed {Ω:Type} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (f0:ℝ → Ω → ℝ) (hf0:∀U:ℝ,0≤U → ∀w,IntegrableOn (fun x => f0 x w) (Ioc 0 U) volume)
    (hinit:∀u:ℝ,0≤u → Measurable[B.F ⊥] (fun w => ∫x in Ioc 0 u,f0 x w))
    (a:ℝ × (Ω × ℝ) → ℝ) (σ:Fin d → ℝ × (Ω × ℝ) → ℝ)
    (ham:Measurable a) (hσm:∀i,Measurable (σ i))
    (hap:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => a (z.1,(z.2.1,z.2.2.val))))
    (hσp:∀i b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => σ i (z.1,(z.2.1,z.2.2.val))))
    (hab:∀ᵐw∂P,∀U,0≤U → ∀b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b, |a (x,(w,r))|≤K)
    (hσb:∀i,∀ᵐw∂P,∀U,0≤U → ∀b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b, |σ i (x,(w,r))|≤K)
    : ∃ N : Fin d → ℝ → HalfClosedTime → Ω → ℝ,
      (∀i,Measurable (fun z:ℝ × (Ω × HalfClosedTime) => N i z.1 z.2.2 z.2.1)) ∧
      (∀i x,LocalMProcessWitness P B.F (N i x)) ∧
      (∀i,∀ᵐx∂volume,0<x → ItoCovarianceFormula P B.F (B.W i) (fun z => -σ i (x,z)) (N i x)) ∧
      (let Price := fun u (t : HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 u,f0 x w+
        (∫s in 0..(t:EReal).toReal,a (x,(w,s)))-∑i,N i x t w))
       (∀ u,0≤u → LocalMProcessWitness P B.F (fun t w => Price u t w-Price u ⊥ w)) →
       (∀ᵐ w ∂P,∀ᵐ r ∂volume,0<r → ∀ᵐ u ∂volume,0<u →
         a (u,(w,r))=∑i,σ i (u,(w,r))*(∫s in 0..u,σ i (s,(w,r)))) ∧
       ∀ U,0≤U → ∃ M : Fin d → HalfClosedTime → Ω → ℝ,
         (∀ i,LocalMProcessWitness P B.F (M i)) ∧
         (∀ i,ItoCovarianceFormula P B.F (B.W i)
           (fun z => -(∫x in Ioc 0 U,σ i (x,z))) (M i)) ∧
         ∀ r,0≤r → Price U (realTimeClamp r)=ᵐ[P]
           (fun w => Real.exp (-(∫x in Ioc 0 U,f0 x w))*Real.exp
             (-(∫s in 0..r,∑i,(∫x in Ioc 0 U,σ i (x,(w,s)))^2)/2+
               ∑i,M i (realTimeClamp r) w))) := by
  have hex i := parameter_ito_global P B i (fun z => -σ i z) (hσm i).neg
    (fun b hb => (hσp i b hb).neg) (by simpa only [abs_neg] using hσb i)
  choose N hNm hN hNI using hex
  exact ⟨N,hNm,hN,hNI,hjm_global_ae_model P B f0 hf0 hinit a σ ham hσm hap hσp hab hσb N hNm hN hNI⟩

#print axioms hjm_constructed
end Asakura.EndToEnd
