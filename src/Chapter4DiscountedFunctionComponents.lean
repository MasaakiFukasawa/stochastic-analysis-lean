import Chapter4DiscountedComponents
import Chapter4DiscountedFeynmanKacTerminal

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

theorem discounted_function_components_integrable
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X : ClosedTime T → Ω → Fin dim → ℝ)
    (hXa : ∀ r,r<⊤ → Measurable[F r] (X r))
    (hXc : ∀ w r,r<⊤ → ContinuousAt (fun u => X u w) r)
    (t : ℝ) (ht : 0≤t) (htT : (t:EReal)<T)
    (v : ℝ → (Fin dim → ℝ) → ℝ)
    (hvc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => v z.1 z.2) {z | 0≤z.1})
    (k g : ℝ × (Fin dim → ℝ) → ℝ) (hk : Continuous k) (hg : Continuous g)
    (hkpos : ∀ r∈Icc 0 t,∀ x,0≤k (t-r,x))
    (L : Ω → ℝ) (hL : MemLp L 2 P)
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 t,|v (t-r) (X (realTimeClamp r) w)|≤L w ∧ |g (t-r,X (realTimeClamp r) w)|≤L w)
 :
    Integrable (fun w => v 0 (X (realTimeClamp t) w)*discountFactor (fun a => k (t-a,X (realTimeClamp a) w)) t) P ∧
    Integrable (fun w => ∫ a in 0..t,g (t-a,X (realTimeClamp a) w)*discountFactor (fun b => k (t-b,X (realTimeClamp b) w)) a) P := by
  let c := fun r : ClosedTime T => (finitePrefixTime t ht r).val
  let Y := fun r w => (t-c r,X r w)
  let fv := fun z : ℝ × (Fin dim → ℝ) => v (max 0 z.1) z.2
  have hfv : Continuous fv := hvc.comp_continuous
    ((continuous_const.max continuous_fst).prodMk continuous_snd) (fun z => show 0≤max 0 z.1 from le_max_left _ _)
  let U := fun r w => fv (Y r w)
  let K := fun r w => k (Y r w)
  let Gs := fun r w => g (Y r w)
  have hYa r hr : Measurable[F r] (Y r) := measurable_const.prodMk (hXa r hr)
  have hYc w r hr : ContinuousAt (fun a => Y a w) r :=
    (continuousAt_const.sub ((continuous_subtype_val.comp (finite_prefix_time_continuous t ht)).continuousAt)).prodMk (hXc w r hr)
  have hcr r (hr : r∈Icc 0 t) : c (realTimeClamp r)=r := finite_prefix_time_of_real t r ht hr htT.le
  have hUr w r (hr : r∈Icc 0 t) : U (realTimeClamp r) w=v (t-r) (X (realTimeClamp r) w) := by
    dsimp only [U,fv,Y]
    rw [hcr r hr,max_eq_right (sub_nonneg.mpr hr.2)]
  have hKr w r (hr : r∈Icc 0 t) : K (realTimeClamp r) w=k (t-r,X (realTimeClamp r) w) := by
    dsimp only [K,Y]
    rw [hcr r hr]
  have hGr w r (hr : r∈Icc 0 t) : Gs (realTimeClamp r) w=g (t-r,X (realTimeClamp r) w) := by
    dsimp only [Gs,Y]
    rw [hcr r hr]
  have hUb : ∀ᵐ w ∂P,∀ r∈Icc 0 t,|U (realTimeClamp r) w|≤L w ∧ |Gs (realTimeClamp r) w|≤L w := by
    filter_upwards [hb] with w hw
    intro r hr
    rw [hUr w r hr,hGr w r hr]
    exact hw r hr
  obtain ⟨hUi,hGi⟩ := discounted_components_integrable P hT F hF hle hnull U K Gs
    (fun r hr => hfv.measurable.comp (hYa r hr)) (fun w r hr => hfv.continuousAt.comp (hYc w r hr))
    (fun r hr => hk.measurable.comp (hYa r hr)) (fun w r hr => hk.continuousAt.comp (hYc w r hr))
    (fun r hr => hg.measurable.comp (hYa r hr)) (fun w r hr => hg.continuousAt.comp (hYc w r hr))
    t ht htT (fun w r hr => by rw [hKr w r hr];exact hkpos r hr _) L hL hUb
  have hDr w r (hr : r∈Icc 0 t) : discountFactor (fun a => K (realTimeClamp a) w) r=
      discountFactor (fun a => k (t-a,X (realTimeClamp a) w)) r := by
    dsimp only [discountFactor]
    congr 2
    apply intervalIntegral.integral_congr
    intro a ha
    exact hKr w a (Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using ha))
  constructor
  · exact hUi.congr (ae_of_all _ fun w => by
      dsimp only
      rw [hUr w t ⟨ht,le_rfl⟩,hDr w t ⟨ht,le_rfl⟩,sub_self])
  · exact hGi.congr (ae_of_all _ fun w => by
      apply intervalIntegral.integral_congr
      intro a ha
      have ha' : a∈Icc 0 t := by simpa only [uIcc_of_le ht] using ha
      dsimp only
      rw [hGr w a ha',hDr w a ha'])

end Asakura.Chapter4
