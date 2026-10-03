import Chapter5ProgressiveDriftVariation
import Chapter3SemimartingaleFiniteSums
import Chapter4BrownianSystem
import Chapter5ClippedDriftIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- A finite-horizon integral equation gives an actual semimartingale
 decomposition, even when the integral equation holds only almost surely. -/
theorem finite_sde_decomposition {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (R : ℝ) (hR : 0≤R) (X N : HalfClosedTime → Ω → ℝ) (ξ : Ω → ℝ)
    (hξ : Measurable[B.F ⊥] ξ)
    (hXa : ∀ t,t<⊤ → Measurable[B.F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (hN : LocalMProcessWitness P B.F N) (b : Ω × ℝ → ℝ)
    (hbp : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => b (z.1,z.2.val)))
    (hbi : ∀ w,Integrable (fun r => b (w,r)) (volume.restrict (Ioc 0 R)))
    (he : ∀ᵐ w ∂P,∀ t∈Icc 0 R,X (realTimeClamp t) w=ξ w+(∫ s in 0..t,b (w,s))+N (realTimeClamp t) w) :
    ∃ A M : HalfClosedTime → Ω → ℝ,
      SemimartingaleDecomposition P B.F (fun t w => X (min (realTimeClamp R) t) w) A M ∧
      (∀ t w,A t w=ξ w+∫ s in 0..(finitePrefixTime R hR t).val,b (w,s)) ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → M t w=N (min (realTimeClamp R) t) w) ∧
      (∀ w r,0≤r → A (realTimeClamp r) w=A ⊥ w+∫ s in 0..r,(Iic R).indicator (fun s => b (w,s)) s) := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨D,hD,hDc,hDe⟩ := progressive_integrable_drift_variation hT B.F B.mono R hR le_top b hbp hbi
  have hξv := continuous_increasing_adapted_variation hT B.F B.mono (fun _ w => ξ w)
    (fun t _ => hξ.mono (B.mono bot_le) le_rfl) (fun _ => monotoneOn_const)
    (fun _ _ _ => continuousAt_const)
  let A := fun t w => ξ w+D t w
  have hA : AdaptedLocalVariationWitness B.F A := hξv.add hD B.mono
  have hAc : ∀ w t,t<⊤ → ContinuousAt (fun s => A s w) t :=
    fun w t _ => continuousAt_const.add (hDc w).continuousAt
  have hRt : realTimeClamp (T:=(⊤:EReal)) R<⊤ := by
    change (realTimeClamp R:EReal)<⊤
    rw [real_time_clamp_eq R hR le_top]
    exact EReal.coe_lt_top R
  have hstop : ∀ t,MeasurableSet[B.F t] {w : Ω | realTimeClamp R≤t} := by
    intro t
    by_cases ht : realTimeClamp (T:=(⊤:EReal)) R≤t <;> simp [ht]
  have hNs := hN.stopped P B.F B.mono B.le (fun _ => realTimeClamp R) hstop
  have hXs t (_ht : t<⊤) : Measurable[B.F t] (fun w => X (min (realTimeClamp R) t) w) :=
    (hXa _ ((min_le_left _ _).trans_lt hRt)).mono (B.mono (min_le_right _ _)) le_rfl
  have hXsc w t (_ht : t<⊤) : ContinuousAt (fun s => X (min (realTimeClamp R) s) w) t :=
    (hXc w _ ((min_le_left _ _).trans_lt hRt)).comp (continuous_const.min continuous_id).continuousAt
  have hdec : ∀ᵐ w ∂P,∀ t : HalfClosedTime,t<⊤ →
      X (min (realTimeClamp R) t) w=A t w+N (min (realTimeClamp R) t) w := by
    filter_upwards [he] with w hw
    intro t _ht
    have hh := hw (finitePrefixTime R hR t).val (finitePrefixTime R hR t).property
    rw [finite_prefix_time_clamp R hR le_top] at hh
    simpa only [A,hDe] using hh
  obtain ⟨hs,hm⟩ := semimartingale_of_ae_decomposition P B.F B.mono
    (fun t w => X (min (realTimeClamp R) t) w) A
    (fun t w => N (min (realTimeClamp R) t) w) hXs hXsc hA hAc hNs hdec
  refine ⟨A,_,hs,fun t w => by simp only [A,hDe],?_⟩
  constructor
  · filter_upwards [hm] with w hw
    exact fun t ht => (hw t ht).symm
  · intro w r hr
    have hp : (finitePrefixTime (T:=(⊤:EReal)) R hR ⊥).val=0 := by
      change (min (0:EReal) (R:EReal)).toReal=0
      rw [min_eq_left (by exact_mod_cast hR),EReal.toReal_zero]
    simp only [A,hDe,hp,intervalIntegral.integral_same,add_zero]
    rw [finite_prefix_time_min R r hR hr le_top,clipped_driver_integral _ R r hR hr]

end Asakura.Chapter11
