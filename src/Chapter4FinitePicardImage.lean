import Chapter4FinitePathLift
import Chapter4DriftNoiseMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- The Picard map actually preserves adapted L² continuous paths.
Neither existence of its integrals nor their square-integrability is an input. -/
theorem finite_picard_image
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hC : LocalCovarianceWitness P F W W C)
    (hCm : ∀ w,MonotoneOn (fun t => C t w) (Iio ⊤))
    (hCc : ∀ w t,t<⊤ → ContinuousAt (fun s => C s w) t)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (L : ℝ) (hL : 0≤L) (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hLip : ∀ x y,(μ x-μ y)^2+(σ x-σ y)^2≤L*(x-y)^2)
    (ξ : Ω → ℝ) (hξ : Measurable[F ⊥] ξ) (hξi : MemLp ξ 2 P)
    (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (hYm : Measurable[m] Y) (hYi : MemLp Y 2 P)
    (hYa : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r)) :
    ∃ (V : Ω → C(Icc (0:ℝ) R,ℝ)) (N : ClosedTime T → Ω → ℝ),
      Measurable[m] V ∧ MemLp V 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => V w r)) ∧
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W
        (fun z => σ (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) N ∧
      ∀ᵐ w ∂P,∀ r,V w r=ξ w+(∫ s in 0..r.val,μ (Y w (projIcc 0 R hR s)))+N (realTimeClamp r.val) w := by
  letI : MeasurableSpace Ω := m
  let U := fun t w => Y w (finitePrefixTime (T := T) R hR t)
  have hU := finite_path_lift_regular F hF R hR hRT.le Y hYa
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨D,N,hD,hN,hNI,hVa,hVc,hrep⟩ := sde_picard_map_exists P hT F hF hle hnull W C U hW hC
    (fun t _ => hU.1 t) (fun w t _ => (hU.2 w).continuousAt) μ σ hμ hσ ξ hξ
    c (fun n => (hc n).le) hcm.monotone hcT hcc
    (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))
  have hDc w t (ht : t<⊤) : ContinuousAt (fun s => D s w) t := by
    convert ((hVc w t ht).sub (hN.path P F w t ht)).sub (continuousAt_const (y := ξ w)) using 1
    funext s
    simp only [Pi.sub_apply]
    ring
  let d := finiteRealPath D R (open_path_stopped_continuous D hDc R hR hRT)
  have hdm : Measurable[m] d := finite_real_path_measurable F hle D R hRT _ hD.adapted
  have hdrep : ∀ᵐ w ∂P,∀ r,d w r=∫ s in 0..r.val,μ (Y w (projIcc 0 R hR s)) := by
    filter_upwards [hrep] with w hw
    intro r
    obtain ⟨j,hj⟩ := hcc (realTimeClamp (T := T) R) (real_time_below R hR hRT)
    have hRj : R≤c j := by
      change (realTimeClamp R:EReal)<(realTimeClamp (c j):EReal) at hj
      rw [real_time_clamp_eq R hR hRT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
      exact (EReal.coe_le_coe_iff.mp hj.le)
    have hd' := hw j r.val ⟨r.property.1,r.property.2.trans hRj⟩
    have hi : (∫ s in 0..r.val,μ (U (realTimeClamp s) w))=
      ∫ s in 0..r.val,μ (Y w (projIcc 0 R hR s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s∈Icc 0 R := Icc_subset_Icc_right r.property.2 (by simpa [uIcc_of_le r.property.1] using hs)
      dsimp only [U]
      rw [finite_path_lift_real R hR hRT.le Y w s hs']
    rw [hi] at hd'
    change D (realTimeClamp r.val) w=_
    linarith
  obtain ⟨hμi,hσi⟩ := coefficient_path_memLp P R L hR hL μ σ hμ hσ hLip Y hYm hYi
  have hgood : ∀ᵐ z ∂P.prod (volume.restrict (Ioc (0:ℝ) R)),z.2∈Ioc (0:ℝ) R := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).2
    exact .of_forall (fun _ => ae_restrict_mem measurableSet_Ioc)
  have hHi : MemLp (fun z : Ω × ℝ => σ (U (realTimeClamp z.2) z.1)) 2
      (P.prod (volume.restrict (Ioc (0:ℝ) R))) := by
    apply (memLp_congr_ae ?_).2 hσi
    filter_upwards [hgood] with z hz
    dsimp only [U]
    rw [finite_path_lift_real R hR hRT.le Y z.1 z.2 ⟨hz.1.le,hz.2⟩]
  obtain ⟨hNc,hi,_⟩ := drift_noise_path_moment P hT F hF hle hnull W C (fun t w => σ (U t w)) N
    hW hC hCm hCc hclock (fun t _ => hσ.measurable.comp (hU.1 t))
    (fun w t _ => (hσ.comp (hU.2 w)).continuousAt) hN hNI R hR hRT hHi
    (fun z => μ (Y z.1 (projIcc 0 R hR z.2)))
    (hμ.measurable.comp (clamped_path_evaluation_measurable R hR Y hYm)) hμi d hdm.aestronglyMeasurable hdrep
  let V := fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w)+(d w+finiteRealPath N R hNc w)
  have hconst : MemLp (fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w)) 2 P := by
    apply hξi.of_le_mul (c := 1) ((ContinuousMap.measurable_iff_eval.mpr (fun _ => hξ.mono (hle _) le_rfl)).aestronglyMeasurable)
    filter_upwards [] with w
    simp only [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg (ξ w))).2 (fun _ => le_rfl)
  refine ⟨V,N,?_,MemLp.add (f := fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w)) (g := fun w => d w+finiteRealPath N R hNc w) hconst hi,?_,hN,hNI,?_⟩
  · exact ((ContinuousMap.measurable_iff_eval.mpr (fun _ => hξ.mono (hle _) le_rfl))).add
      (hdm.add (finite_real_path_measurable F hle N R hRT hNc (hN.adapted P F)))
  · intro r
    have ht := real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hRT)
    exact (hξ.mono (hF bot_le) le_rfl).add ((hD.adapted _ ht).add (hN.adapted P F _ ht))
  · filter_upwards [hdrep] with w hw
    intro r
    change ξ w+(d w r+N (realTimeClamp r.val) w)=_
    rw [hw]
    ring

end Asakura.Chapter4
