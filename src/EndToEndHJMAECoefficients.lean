import EndToEndFiniteCoefficientRepair

open MeasureTheory Set Filter
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The finite-maturity HJM construction under almost-sure local bounds on
 the maturity interval alone. Coefficient representatives are constructed,
 with their common-event agreement explicitly included in the conclusion. -/
theorem hjm_finite_maturity_ae_coefficients {Ω:Type} {m:MeasurableSpace Ω}
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
    (hab:∀ᵐ w ∂P,∀ b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀ r∈Icc 0 b,|a (x,(w,r))|≤K)
    (hσb:∀i,∀ᵐ w ∂P,∀ b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀ r∈Icc 0 b,|σ i (x,(w,r))|≤K) :
    ∃ a' : ℝ × (Ω × ℝ) → ℝ, ∃ σ' : Fin d → ℝ × (Ω × ℝ) → ℝ,
      (∀ᵐ w ∂P,∀ x∈Icc 0 U,∀ r,a' (x,(w,r))=a (x,(w,r))) ∧
      (∀ i,∀ᵐ w ∂P,∀ x∈Icc 0 U,∀ r,σ' i (x,(w,r))=σ i (x,(w,r))) ∧
    ∃ N : Fin d → ℝ → HalfClosedTime → Ω → ℝ,
      (∀ i,Measurable (fun z : ℝ × (Ω × HalfClosedTime) => N i z.1 z.2.2 z.2.1)) ∧
      (∀ i x,LocalMProcessWitness P B.F (N i x)) ∧
      (∀ i,∀ᵐ x ∂volume.restrict (Ioc 0 U),
        ItoCovarianceFormula P B.F (B.W i) (fun z => -σ' i (x,z)) (N i x)) ∧
      (let Price := fun u (t : HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 u,f0 x+
        (∫s in 0..(t:EReal).toReal,a' (x,(w,s)))-∑i,N i x t w))
       (∀ u∈Icc 0 U,LocalMProcessWitness P B.F (fun t w => Price u t w-Price u ⊥ w)) →
       ∀ R,0≤R → ∀ᵐ w ∂P,∀ᵐ r ∂volume,r∈Ioo 0 R →
         ∀ᵐ u ∂volume,u∈Ioo 0 U →
           a' (u,(w,r))=∑i,σ' i (u,(w,r))*(∫s in 0..u,σ' i (s,(w,r)))) := by
  obtain ⟨a',ham',hap',hab',hae⟩ := finite_coefficient_repair P B (Icc 0 U) measurableSet_Icc a ham hap hab
  have hex i := finite_coefficient_repair P B (Icc 0 U) measurableSet_Icc (σ i) (hσm i) (hσp i) (hσb i)
  choose σ' hσm' hσp' hσb' hσe using hex
  exact ⟨a',σ',hae,hσe,hjm_finite_maturity_constructed P B U hU f0 hf0 a' σ'
    ham' hσm' hap' hσp' hab' hσb'⟩

#print axioms hjm_finite_maturity_ae_coefficients
end Asakura.EndToEnd
