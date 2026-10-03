import Chapter5BSDEFiniteEnergyData
import Chapter5FrozenSemimartingale
import Chapter2ContinuousIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma semimartingale_real_measurable
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t≤m)
    (Y V M : ClosedTime T → Ω → ℝ) (hY : SemimartingaleDecomposition P F Y V M)
    (hc : ∀ w,Continuous (fun t => Y t w))
    (hfinite : ∀ r : ℝ,realTimeClamp (T := T) r<⊤) :
    Measurable (fun z : Ω × ℝ => Y (realTimeClamp z.2) z.1) := by
  have hm r : Measurable (Y (realTimeClamp r)) := by
    have he : Y (realTimeClamp r)=fun w => V (realTimeClamp r) w+M (realTimeClamp r) w :=
      funext (hY.decomposition _ (hfinite r))
    rw [he]
    exact ((hY.variation.adapted _ (hfinite r)).add (hY.martingale.adapted P F _ (hfinite r))).mono (hle _) le_rfl
  exact (measurable_uncurry_of_continuous_of_measurable
    (fun w => (hc w).comp real_time_clamp_continuous) hm).comp measurable_swap

lemma finite_semimartingale_progressive
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (Y V M : ClosedTime T → Ω → ℝ) (hY : SemimartingaleDecomposition P F Y V M)
    (hc : ∀ w,Continuous (fun t => Y t w)) (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => Y (realTimeClamp z.2.val) z.1) := by
  apply continuous_adapted_real_progressive F hF (fun z : Ω × ℝ => Y (realTimeClamp z.2) z.1) R hR
  · intro r hr
    have ht : realTimeClamp (T := T) r<⊤ := by
      change (realTimeClamp r:EReal)<T
      rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hRT.le)]
      exact (EReal.coe_le_coe hr.2).trans_lt hRT
    have he : Y (realTimeClamp r)=fun w => V (realTimeClamp r) w+M (realTimeClamp r) w :=
      funext (hY.decomposition _ ht)
    change Measurable[F (realTimeClamp r)] (Y (realTimeClamp r))
    rw [he]
    exact (hY.variation.adapted _ ht).add (hY.martingale.adapted P F _ ht)
  · exact fun w => ((hc w).comp real_time_clamp_continuous).continuousOn

lemma common_finite_process_product_congr
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (X Y : Ω × ℝ → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (he : ∀ᵐ w ∂P,∀ r∈Icc 0 R,X (w,r)=Y (w,r)) :
    X =ᵐ[P.prod (volume.restrict (Ioc 0 R))] Y := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hX hY)).mpr
  filter_upwards [he] with w hw
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact hw r ⟨hr.1.le,hr.2⟩

end Asakura.Chapter5
