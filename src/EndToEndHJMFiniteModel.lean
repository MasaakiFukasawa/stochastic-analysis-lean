import EndToEndHJMFiniteMaturity
import EndToEndHJMExponential

open MeasureTheory Set Filter
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The pointwise HJM drift on a finite positive maturity interval, derived
from the original coefficients and local-martingale bond prices. Coefficients
may be zero-extended outside this maturity interval. -/
theorem hjm_finite_maturity_model {Ω:Type} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (U : ℝ) (hU : 0≤U) (f0:ℝ → ℝ) (hf0:IntegrableOn f0 (Ioc 0 U) volume)
    (a:ℝ × (Ω × ℝ) → ℝ) (σ:Fin d → ℝ × (Ω × ℝ) → ℝ)
    (ham:Measurable a) (hσm:∀i,Measurable (σ i))
    (hap:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => a (z.1,(z.2.1,z.2.2.val))))
    (hσp:∀i b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => σ i (z.1,(z.2.1,z.2.2.val))))
    (hab:∀w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |a (x,(w,r))|≤K)
    (hσb:∀i w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |σ i (x,(w,r))|≤K) :
    ∃ N : Fin d → ℝ → HalfClosedTime → Ω → ℝ,
      (∀ i,Measurable (fun z : ℝ × (Ω × HalfClosedTime) => N i z.1 z.2.2 z.2.1)) ∧
      (∀ i x,LocalMProcessWitness P B.F (N i x)) ∧
      (∀ i,∀ᵐ x ∂volume.restrict (Ioc 0 U),
        ItoCovarianceFormula P B.F (B.W i) (fun z => -σ i (x,z)) (N i x)) ∧
      (let Price := fun u (t : HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 u,f0 x+
        (∫s in 0..(t:EReal).toReal,a (x,(w,s)))-∑i,N i x t w))
       (∀ u∈Icc 0 U,LocalMProcessWitness P B.F (fun t w => Price u t w-Price u ⊥ w)) →
       (∀ R,0≤R → ∀ᵐ w ∂P,∀ᵐ r ∂volume,r∈Ioo 0 R →
         ∀ᵐ u ∂volume,u∈Ioo 0 U →
           a (u,(w,r))=∑i,σ i (u,(w,r))*(∫s in 0..u,σ i (s,(w,r)))) ∧
       ∀ u∈Icc 0 U,∃ M : Fin d → HalfClosedTime → Ω → ℝ,
         (∀ i,LocalMProcessWitness P B.F (M i)) ∧
         (∀ i,ItoCovarianceFormula P B.F (B.W i)
           (fun z => -(∫x in Ioc 0 u,σ i (x,z))) (M i)) ∧
         ∀ r,0≤r → Price u (realTimeClamp r)=ᵐ[P]
           (fun w => Real.exp (-(∫x in Ioc 0 u,f0 x))*Real.exp
             (-(∫s in 0..r,∑i,(∫x in Ioc 0 u,σ i (x,(w,s)))^2)/2+
               ∑i,M i (realTimeClamp r) w))) := by
  obtain ⟨N,hNm,hN,hNI,hD⟩ := hjm_finite_maturity_constructed P B U hU f0 hf0 a σ
    ham hσm hap hσp hab hσb
  refine ⟨N,hNm,hN,hNI,?_⟩
  intro Price hPrice
  refine ⟨hD hPrice,?_⟩
  intro u hu
  have hsub : Ioc (0:ℝ) u ⊆ Ioc 0 U := fun x hx => ⟨hx.1,hx.2.trans hu.2⟩
  have hni i : ∀ᵐ x ∂volume.restrict (Ioc 0 u),
      ItoCovarianceFormula P B.F (B.W i) (fun z => -σ i (x,z)) (N i x) :=
    ae_mono (Measure.restrict_mono hsub le_rfl) (hNI i)
  obtain ⟨M,hM,hMI,_,he⟩ := hjm_exponential_from_forward_integrals P B
    (volume.restrict (Ioc 0 u)) f0 (hf0.mono_set hsub) a σ
    ham hσm hap hσp hab hσb N hN hni hNm (hPrice u hu)
  exact ⟨M,hM,hMI,he⟩

#print axioms hjm_finite_maturity_model
end Asakura.EndToEnd
