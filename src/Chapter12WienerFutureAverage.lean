import Chapter12FiniteWienerFutureConstructed
import Chapter12ConstructedFutureProgressive

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The same finite Wiener map supplies a progressive future-Gaussian
average, with its fixed-time integral exactly equal to integration against
the actual future law. -/
theorem wiener_future_average_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (T : ℝ) (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hfuture : ∀ u,∃ N : HalfClosedTime → Ω → ℝ,ContinuousM2Witness P B.F N ∧
      (W u : Ω → ℝ)=ᵐ[P] N ⊤ ∧
      ∀ a,0≤a → (W (finiteFuturePart T a u) : Ω → ℝ)=ᵐ[P]
        fun w => N ⊤ w-N (realTimeClamp a) w)
    (n : ℕ) (u : Fin n → FiniteWienerHilbert d T)
    (f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    ∃ N : Fin n → HalfClosedTime → Ω → ℝ,
      (∀ i,ContinuousM2Witness P B.F (N i)) ∧
      (∀ i,(W (u i) : Ω → ℝ)=ᵐ[P] N i ⊤) ∧
      (∀ a,0≤a → (fun w i => W (finiteFuturePart T a (u i)) w)=ᵐ[P]
        fun w i => N i ⊤ w-N i (realTimeClamp a) w) ∧
      @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) T => ∫ w,
          f ((fun i => N i (realTimeClamp z.2.val) z.1),
            (fun i => N i ⊤ w-N i (realTimeClamp z.2.val) w)) ∂P) ∧
      (∀ t : Icc (0:ℝ) T,∀ w,
        (∫ v,f ((fun i => N i (realTimeClamp t.val) w),
          (fun i => N i ⊤ v-N i (realTimeClamp t.val) v)) ∂P)=
        ∫ y,f ((fun i => N i (realTimeClamp t.val) w),y)
          ∂(P.map (fun v i => W (finiteFuturePart T t.val (u i)) v))) := by
  choose N hN hterm hfutureN using fun i => hfuture (u i)
  have he a (ha : 0≤a) : (fun w i => W (finiteFuturePart T a (u i)) w)=ᵐ[P]
      fun w i => N i ⊤ w-N i (realTimeClamp a) w := by
    filter_upwards [ae_all_iff.mpr (fun i => hfutureN i a ha)] with w hw
    exact funext hw
  refine ⟨N,hN,hterm,he,
    continuous_integral_future_average_progressive P B.F B.mono B.le n N hN T f hf,?_⟩
  intro t w
  have hm : Measurable (fun v i => W (finiteFuturePart T t.val (u i)) v) :=
    measurable_pi_iff.mpr (fun i => (Lp.stronglyMeasurable _).measurable)
  have hg : Measurable (fun y => f ((fun i => N i (realTimeClamp t.val) w),y)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [integral_map (μ := P) hm.aemeasurable hg.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [he t.val t.property.1] with v hv
  rw [hv]

end Asakura.Chapter12
#print axioms Asakura.Chapter12.wiener_future_average_constructed
