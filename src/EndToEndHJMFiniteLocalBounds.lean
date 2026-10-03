import EndToEndHJMFiniteGiven
import EndToEndFiniteParameterExtension

open MeasureTheory Set Filter
open scoped Classical
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The pointwise HJM drift on a finite positive maturity interval, derived
from the original coefficients and local-martingale bond prices. Coefficients
may be zero-extended outside this maturity interval. -/
theorem hjm_finite_drift_local_bounds {Ω:Type} {m:MeasurableSpace Ω}
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
    (hab:∀w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b, |a (x,(w,r))|≤K)
    (hσb:∀i w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b, |σ i (x,(w,r))|≤K)
    (N : Fin d → ℝ → HalfClosedTime → Ω → ℝ)
    (hNm : ∀i,Measurable (fun z:ℝ × (Ω × HalfClosedTime) => N i z.1 z.2.2 z.2.1))
    (hN : ∀i x,LocalMProcessWitness P B.F (N i x))
    (hNI : ∀i,∀ᵐx∂volume.restrict (Ioc 0 U),
      ItoCovarianceFormula P B.F (B.W i) (fun z => -σ i (x,z)) (N i x)) :
      (let Price := fun u (t : HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 u,f0 x+
        (∫s in 0..(t:EReal).toReal,a (x,(w,s)))-∑i,N i x t w))
       (∀ u∈Icc 0 U,LocalMProcessWitness P B.F (fun t w => Price u t w-Price u ⊥ w)) →
       ∀ R,0≤R → ∀ᵐ w ∂P,∀ᵐ r ∂volume,r∈Ioo 0 R →
         ∀ᵐ u ∂volume,u∈Ioo 0 U →
           a (u,(w,r))=∑i,σ i (u,(w,r))*(∫s in 0..u,σ i (s,(w,r)))) := by
  classical
  intro Price hPrice R hR
  let a' := fun z : ℝ × (Ω × ℝ) => @ite ℝ (z.1∈Icc 0 U) (Classical.propDecidable _) (a z) 0
  let σ' := fun i (z : ℝ × (Ω × ℝ)) => @ite ℝ (z.1∈Icc 0 U) (Classical.propDecidable _) (σ i z) 0
  obtain ⟨ham',hap',hab',ha⟩ := finite_parameter_extension B.F (Icc 0 U) measurableSet_Icc a ham hap hab
  have hσ i := finite_parameter_extension B.F (Icc 0 U) measurableSet_Icc (σ i) (hσm i) (hσp i) (hσb i)
  have hni i : ∀ᵐx∂volume.restrict (Ioc 0 U),
      ItoCovarianceFormula P B.F (B.W i) (fun z => -σ' i (x,z)) (N i x) := by
    filter_upwards [hNI i,ae_restrict_mem measurableSet_Ioc] with x hx hxi
    simpa only [σ',if_pos (show x∈Icc 0 U from ⟨hxi.1.le,hxi.2⟩)] using hx
  let Price' := fun u (t:HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 u,f0 x+
    (∫s in 0..(t:EReal).toReal,a' (x,(w,s)))-∑i,N i x t w))
  have he u (hu:u∈Icc 0 U) t w : Price' u t w=Price u t w := by
    apply congrArg (fun x : ℝ => Real.exp (-x))
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    have hxi : x∈Icc 0 U := ⟨hx.1.le,hx.2.trans hu.2⟩
    simp only [a',if_pos hxi]
  have hp u (hu:u∈Icc 0 U) : LocalMProcessWitness P B.F (fun t w => Price' u t w-Price' u ⊥ w) := by
    convert hPrice u hu using 1
    funext t w
    rw [he u hu t w,he u hu ⊥ w]
  have hd := hjm_finite_drift_given P B U hU f0 hf0 a' σ' (by simpa only [a'] using ham')
    (fun i => by simpa only [σ'] using (hσ i).1) (by simpa only [a'] using hap')
    (fun i => by simpa only [σ'] using (hσ i).2.1) (by simpa only [a'] using hab')
    (fun i => by simpa only [σ'] using (hσ i).2.2.1)
    N hNm hN hni hp R hR
  filter_upwards [hd] with w hw
  filter_upwards [hw] with r hr hri
  filter_upwards [hr hri] with u hu hui
  have huU : u∈Icc 0 U := ⟨hui.1.le,hui.2.le⟩
  have hi i : (∫s in 0..u,σ' i (s,(w,r)))=(∫s in 0..u,σ i (s,(w,r))) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsi : s∈Icc 0 U := ⟨(uIcc_of_le hui.1.le ▸ hs).1,(uIcc_of_le hui.1.le ▸ hs).2.trans hui.2.le⟩
    simp only [σ',if_pos hsi]
  simpa only [a',σ',if_pos huU,hi] using hu hui

#print axioms hjm_finite_drift_local_bounds
end Asakura.EndToEnd
