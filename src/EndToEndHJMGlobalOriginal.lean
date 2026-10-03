import EndToEndHJMFiniteLocalBounds
import EndToEndHJMExhaustion

open MeasureTheory Set Filter
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The pointwise HJM drift on a finite positive maturity interval, derived
from the original coefficients and local-martingale bond prices. Coefficients
may be zero-extended outside this maturity interval. -/
theorem hjm_global_original_drift {Ω:Type} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (f0:ℝ → ℝ) (hf0:∀U:ℝ,0≤U → IntegrableOn f0 (Ioc 0 U) volume)
    (a:ℝ × (Ω × ℝ) → ℝ) (σ:Fin d → ℝ × (Ω × ℝ) → ℝ)
    (ham:Measurable a) (hσm:∀i,Measurable (σ i))
    (hap:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => a (z.1,(z.2.1,z.2.2.val))))
    (hσp:∀i b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => σ i (z.1,(z.2.1,z.2.2.val))))
    (hab:∀w U,0≤U → ∀b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b, |a (x,(w,r))|≤K)
    (hσb:∀i w U,0≤U → ∀b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b, |σ i (x,(w,r))|≤K)
    (N : Fin d → ℝ → HalfClosedTime → Ω → ℝ)
    (hNm : ∀i,Measurable (fun z:ℝ × (Ω × HalfClosedTime) => N i z.1 z.2.2 z.2.1))
    (hN : ∀i x,LocalMProcessWitness P B.F (N i x))
    (hNI : ∀i x,
      ItoCovarianceFormula P B.F (B.W i) (fun z => -σ i (x,z)) (N i x)) :
      (let Price := fun u (t : HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 u,f0 x+
        (∫s in 0..(t:EReal).toReal,a (x,(w,s)))-∑i,N i x t w))
       (∀ u,0≤u → LocalMProcessWitness P B.F (fun t w => Price u t w-Price u ⊥ w)) →
       ∀ᵐ w ∂P,∀ᵐ r ∂volume,0<r → ∀ᵐ u ∂volume,0<u →
         a (u,(w,r))=∑i,σ i (u,(w,r))*(∫s in 0..u,σ i (s,(w,r)))) := by
  intro Price hPrice
  apply positive_quadrant_ae_of_boxes P
    (fun w r u => a (u,(w,r))=∑i,σ i (u,(w,r))*(∫s in 0..u,σ i (s,(w,r))))
  intro k
  have hk : 0≤(k:ℝ)+1 := by positivity
  exact hjm_finite_drift_local_bounds P B ((k:ℝ)+1) hk f0 (hf0 _ hk) a σ ham hσm hap hσp
    (fun w => hab w _ hk) (fun i w => hσb i w _ hk) N hNm hN
    (fun i => Filter.Eventually.of_forall (hNI i)) (fun u hu => hPrice u hu.1) _ hk

#print axioms hjm_global_original_drift
end Asakura.EndToEnd
