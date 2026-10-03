import Chapter11FiniteIntegral
import Chapter11HedgeEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The finite-horizon isometry for a constructed terminal integral.
It is derived from quadratic variation, not imposed on the representation. -/
theorem finite_ito_isometry {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H : Ω × ℝ → ℝ) (hH : Measurable H) (T : ℝ) (hT : 0≤T)
    (hp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) T => H (z.1,z.2.val)))
    (hi : Integrable (fun z => H z^2) (P.prod (volume.restrict (Ioo 0 T))))
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0)
      (fun z => (Iic T).indicator (fun t => H (z.1,t)) z.2) N) :
    (∫ z,H z^2 ∂P.prod (volume.restrict (Ioo 0 T)))=∫ w,(N (realTimeClamp T) w)^2 ∂P := by
  let G := fun z : Ω × ℝ => (Iic T).indicator (fun t => H (z.1,t)) z.2
  have hG : Measurable G := by
    change Measurable ((Prod.snd ⁻¹' Iic T).indicator H)
    exact hH.indicator (measurableSet_Iic.preimage measurable_snd)
  have hG2 := finite_zero_extension_L2 P H hH T hi
  have hGi : Integrable (fun z => G z^2) (P.prod (volume.restrict (Ioi 0))) :=
    (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG2
  have hpath : ∀ᵐ w ∂P,Integrable (fun t => G (w,t)^2) (volume.restrict (Ioi 0)) := hGi.prod_right_ae
  have hGp d (hd : 0<d) := progressive_finite_zero_extension (fun r => B.F (realTimeClamp r))
    (B.mono.comp real_time_clamp_mono) T hT H hp d
  have hGp' : ∀ d,0<d → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => G (z.1,z.2.val)) := hGp
  have hpath' d (hd : 0<d) : ∀ᵐ w ∂P,IntervalIntegrable (fun t => G (w,t)^2) volume 0 d := by
    filter_upwards [hpath] with w hw
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le).mpr (hw.mono_measure (Measure.restrict_mono (fun t ht => ht.1) le_rfl))
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (T:=(⊤:EReal)) (by simp)
  have hNl := continuous_m2_is_local P B.F B.mono B.le
    (fun n => realTimeClamp (c n)) hct.monotone hcut hcc N hN
  obtain ⟨_,he,_⟩ := brownian_prefix_energy_of_price P B G hGp' hpath' N N hNl hNI hN T hT
    (fun t ht => Filter.EventuallyEq.rfl)
  have hmeasure : volume.restrict (Ioo (0:ℝ) T)=volume.restrict (Ioc 0 T) := restrict_Ioo_eq_restrict_Ioc
  have hi' : Integrable (fun z => H z^2) (P.prod (volume.restrict (Ioc 0 T))) := by rwa [hmeasure] at hi
  rw [hmeasure,integral_prod _ hi']
  rw [←he]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  change (∫ t in Ioc 0 T,H (w,t)^2)=(∫ t in 0..T,G (w,t)^2)
  rw [intervalIntegral.integral_of_le hT]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  simp only [G,Set.indicator_of_mem (show t∈Iic T from ht.2)]

end Asakura.Chapter11
