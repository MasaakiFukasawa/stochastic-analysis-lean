import Chapter4DiscountedProcessConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency false

/-- Construct a discounted process with its source integral and prove
its adaptedness, continuity, and uniform random bound. -/
theorem discounted_components_integrable
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (U K G : ClosedTime T → Ω → ℝ)
    (hUa : ∀ t,t<⊤ → Measurable[F t] (U t))
    (hUc : ∀ w t,t<⊤ → ContinuousAt (fun s => U s w) t)
    (hKa : ∀ t,t<⊤ → Measurable[F t] (K t))
    (hKc : ∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t)
    (hGa : ∀ t,t<⊤ → Measurable[F t] (G t))
    (hGc : ∀ w t,t<⊤ → ContinuousAt (fun s => G s w) t)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hKpos : ∀ w r,r∈Icc 0 R → 0≤K (realTimeClamp r) w)
    (B : Ω → ℝ) (hB : MemLp B 2 P)
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|U (realTimeClamp r) w|≤B w ∧ |G (realTimeClamp r) w|≤B w)
 :
    Integrable (fun w => U (realTimeClamp R) w*discountFactor (fun a => K (realTimeClamp a) w) R) P ∧
    Integrable (fun w => ∫ a in 0..R,G (realTimeClamp a) w*discountFactor (fun b => K (realTimeClamp b) w) a) P := by
  have hB0 : ∀ᵐ w ∂P,0≤B w := hb.mono fun w hw => (abs_nonneg _).trans (hw 0 ⟨le_rfl,hR⟩).1
  have hUB : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|U (realTimeClamp r) w|≤B w ∧ |(0:ℝ)|≤B w := by
    filter_upwards [hb,hB0] with w hw hw0
    exact fun r hr => ⟨(hw r hr).1,by simpa only [abs_zero] using hw0⟩
  have hGB : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|(0:ℝ)|≤B w ∧ |G (realTimeClamp r) w|≤B w := by
    filter_upwards [hb,hB0] with w hw hw0
    exact fun r hr => ⟨by simpa only [abs_zero] using hw0,(hw r hr).2⟩
  obtain ⟨V,hVa,hVc,hVe,hVb⟩ := discounted_process_construction P hT F hF hle hnull U K (fun _ _ => 0)
    hUa hUc hKa hKc (fun _ _ => measurable_const) (fun _ _ _ => continuousAt_const)
    R hR hRT hKpos B hB hUB
  obtain ⟨J,hJa,hJc,hJe,hJb⟩ := discounted_process_construction P hT F hF hle hnull (fun _ _ => 0) K G
    (fun _ _ => measurable_const) (fun _ _ _ => continuousAt_const) hKa hKc hGa hGc
    R hR hRT hKpos B hB hGB
  have hdom : Integrable (fun w => (1+R)*B w) P := (hB.const_mul (1+R)).integrable (by norm_num)
  have hVi : Integrable (V (realTimeClamp R)) P := hdom.mono'
    (((hVa _ (real_time_below R hR hRT)).mono (hle _) le_rfl).aestronglyMeasurable)
    (hVb.mono fun w hw => hw _ le_rfl)
  have hJi : Integrable (J (realTimeClamp R)) P := hdom.mono'
    (((hJa _ (real_time_below R hR hRT)).mono (hle _) le_rfl).aestronglyMeasurable)
    (hJb.mono fun w hw => hw _ le_rfl)
  constructor
  · exact hVi.congr (ae_of_all _ fun w => by
      simpa only [zero_mul,intervalIntegral.integral_zero,add_zero] using hVe w R ⟨hR,le_rfl⟩)
  · exact hJi.congr (ae_of_all _ fun w => by
      simpa only [zero_mul,zero_add] using hJe w R ⟨hR,le_rfl⟩)

end Asakura.Chapter4
