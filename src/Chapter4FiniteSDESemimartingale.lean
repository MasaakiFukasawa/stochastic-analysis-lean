import Chapter5ProgressiveDriftVariation
import Chapter5ClippedDriftIntegral
import Chapter5FrozenCoordinates
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- A finite-horizon restriction of the actual SDE has an explicitly
constructed adapted variation part. No bounded-variation assumption on
its drift primitive is added. -/
theorem finite_sde_semimartingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X N G : ClosedTime T → Ω → ℝ) (ξ : Ω → ℝ)
    (hξ : Measurable[F ⊥] ξ) (hN : LocalMProcessWitness P F N)
    (hGa : ∀ t,t<⊤ → Measurable[F t] (G t))
    (hGc : ∀ w t,t<⊤ → ContinuousAt (fun s => G s w) t)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (he : ∀ᵐ w ∂P,∀ r∈Icc 0 R,X (realTimeClamp r) w=
      ξ w+(∫ s in 0..r,G (realTimeClamp s) w)+N (realTimeClamp r) w) :
    ∃ Y A : ClosedTime T → Ω → ℝ,
      SemimartingaleDecomposition P F Y A (fun t w => N (min (realTimeClamp R) t) w) ∧
      (∀ w,Continuous (fun t => Y t w)) ∧
      (∀ᵐ w ∂P,∀ t,Y t w=X (min (realTimeClamp R) t) w) ∧
      (∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=A ⊥ w+
        ∫ s in 0..r,(Iic R).indicator (fun s => G (realTimeClamp s) w) s) := by
  let H := fun z : Ω × ℝ => G (realTimeClamp z.2) z.1
  have hHc w : ContinuousOn (fun r => H (w,r)) (Icc 0 R) := by
    intro r hr
    exact ((hGc w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hRT))).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hHp := continuous_adapted_real_progressive F hF H R hR
    (fun r hr => hGa _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hRT))) hHc
  obtain ⟨D,hDv,hDc,hDe⟩ := progressive_integrable_drift_variation hT F hF R hR hRT.le H hHp
    (fun w => ((hHc w).intervalIntegrable_of_Icc hR).1)
  let A := fun t w => ξ w+D t w
  let Y := fun t w => A t w+N (min (realTimeClamp (T := T) R) t) w
  have hAv := (frozen_coordinate_semimartingale P hT F hF ξ hξ).variation.add hDv hF
  have hNc := open_path_stopped_continuous N (hN.path P F) R hR hRT
  have hNl := hN.stopped P F hF hle (fun _ => realTimeClamp R)
    (fun t => by by_cases h : realTimeClamp (T := T) R≤t <;> simp [h])
  have hYc w : Continuous (fun t => Y t w) := (continuous_const.add (hDc w)).add (hNc w)
  have hD0 w : D ⊥ w=0 := by
    rw [hDe]
    have hp : (finitePrefixTime (T := T) R hR ⊥).val=0 := by
      change (min (0:EReal) (R:EReal)).toReal=0
      rw [min_eq_left (by exact_mod_cast hR),EReal.toReal_zero]
    rw [hp,intervalIntegral.integral_same]
  refine ⟨Y,A,⟨hAv,hNl,fun w _ _ => (hYc w).continuousAt,fun _ _ _ => rfl⟩,hYc,?_,?_⟩
  · filter_upwards [he] with w hw
    intro t
    let r := (finitePrefixTime (T := T) R hR t).val
    have hr : r∈Icc 0 R := (finitePrefixTime (T := T) R hR t).property
    have hrt : realTimeClamp (T := T) r=min (realTimeClamp R) t := finite_prefix_time_clamp R hR hRT.le t
    have hh := hw r hr
    rw [hrt] at hh
    dsimp only [Y,A]
    rw [hDe]
    exact hh.symm
  · intro w r hr hrT
    dsimp only [A]
    rw [hD0,hDe,finite_prefix_time_min R r hR hr hrT.le,clipped_driver_integral _ R r hR hr,add_zero]

end Asakura.Chapter4
