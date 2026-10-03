import EndToEndHJMRandomInitial
import EndToEndFiniteMaturityDrift

open MeasureTheory Set Filter
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The pointwise HJM drift on a finite positive maturity interval, derived
from the original coefficients and local-martingale bond prices. Coefficients
may be zero-extended outside this maturity interval. -/
theorem hjm_finite_random_drift_given {Ω:Type} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (U : ℝ) (hU : 0≤U) (f0:ℝ → Ω → ℝ) (hf0:∀w,IntegrableOn (fun x => f0 x w) (Ioc 0 U) volume)
    (hinit:∀u∈Icc 0 U,Measurable[B.F ⊥] (fun w => ∫x in Ioc 0 u,f0 x w))
    (a:ℝ × (Ω × ℝ) → ℝ) (σ:Fin d → ℝ × (Ω × ℝ) → ℝ)
    (ham:Measurable a) (hσm:∀i,Measurable (σ i))
    (hap:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => a (z.1,(z.2.1,z.2.2.val))))
    (hσp:∀i b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => σ i (z.1,(z.2.1,z.2.2.val))))
    (hab:∀w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |a (x,(w,r))|≤K)
    (hσb:∀i w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |σ i (x,(w,r))|≤K)
    (N : Fin d → ℝ → HalfClosedTime → Ω → ℝ)
    (hNm : ∀i,Measurable (fun z:ℝ × (Ω × HalfClosedTime) => N i z.1 z.2.2 z.2.1))
    (hN : ∀i x,LocalMProcessWitness P B.F (N i x))
    (hNI : ∀i,∀ᵐx∂volume.restrict (Ioc 0 U),
      ItoCovarianceFormula P B.F (B.W i) (fun z => -σ i (x,z)) (N i x)) :
      (let Price := fun u (t : HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 u,f0 x w+
        (∫s in 0..(t:EReal).toReal,a (x,(w,s)))-∑i,N i x t w))
       (∀ u∈Icc 0 U,LocalMProcessWitness P B.F (fun t w => Price u t w-Price u ⊥ w)) →
       ∀ R,0≤R → ∀ᵐ w ∂P,∀ᵐ r ∂volume,r∈Ioo 0 R →
         ∀ᵐ u ∂volume,u∈Ioo 0 U →
           a (u,(w,r))=∑i,σ i (u,(w,r))*(∫s in 0..u,σ i (s,(w,r)))) := by
  intro Price hPrice R hR
  have hd u (hu : u∈Icc 0 U) : ∀ᵐw∂P,∀ᵐr∂volume,r∈Ioo 0 R →
      (∫x in Ioc 0 u,a (x,(w,r)))=(∑i,(∫x in Ioc 0 u,σ i (x,(w,r)))^2)/2 := by
    have hsub : Ioc (0:ℝ) u ⊆ Ioc 0 U := fun x hx => ⟨hx.1,hx.2.trans hu.2⟩
    have hni i := ae_mono (Measure.restrict_mono hsub le_rfl) (hNI i)
    obtain ⟨_,_,_,hD,_⟩ := hjm_exponential_random_initial P B (volume.restrict (Ioc 0 u))
      f0 (fun w => (hf0 w).mono_set hsub) (hinit u hu) a σ ham hσm hap hσp hab hσb N hN hni hNm (hPrice u hu)
    exact hD R hR
  have hq q := hd (intervalClamp 0 U hU (q:ℚ)) (intervalClamp_mem 0 U hU q)
  filter_upwards [ae_all_iff.mpr hq] with w hw
  filter_upwards [ae_all_iff.mpr hw] with r hr
  intro hri
  have hai : IntervalIntegrable (fun x => a (x,(w,r))) volume 0 U := by
    obtain ⟨K,hK,hb⟩ := hab w r hri.1.le
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hU]
    exact Integrable.of_bound (ham.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable K
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x r ⟨hri.1.le,le_rfl⟩))
  have hsi i : IntervalIntegrable (fun x => σ i (x,(w,r))) volume 0 U := by
    obtain ⟨K,hK,hb⟩ := hσb i w r hri.1.le
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hU]
    exact Integrable.of_bound ((hσm i).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable K
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x r ⟨hri.1.le,le_rfl⟩))
  apply (finite_maturity_drift U hU (fun x => a (x,(w,r)))
    (fun i x => σ i (x,(w,r))) hai hsi ?_).2
  intro q
  simpa only [intervalIntegral.integral_of_le (intervalClamp_mem 0 U hU (q:ℝ)).1] using hr q hri

#print axioms hjm_finite_random_drift_given
end Asakura.EndToEnd
