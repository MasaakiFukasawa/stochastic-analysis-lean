import Chapter2FiniteTimeProjection
import Chapter9CompensatedMartingale

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- A bounded continuous martingale on a finite real interval, frozen at
 its right endpoint, belongs to the previously constructed process space. -/
theorem finite_interval_bounded_martingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → MeasurableSpace Ω) (hle : ∀ r,F r≤m)
    (Y : ℝ → Ω → ℝ) (b : ℝ) (hb : 0≤b)
    (hm : ∀ r∈Icc 0 b,Measurable[F r] (Y r))
    (hc : ∀ w,ContinuousOn (fun r => Y r w) (Icc 0 b))
    (C : ℝ) (hbound : ∀ r∈Icc 0 b,∀ w,‖Y r w‖≤C)
    (hce : ∀ s t,0≤s → s≤t → t≤b → P[Y t|F s]=ᵐ[P] Y s)
    (hz : ∀ w,Y 0 w=0) :
    (fun (t : HalfClosedTime) w => Y (finitePrefixTime b hb t).val w) ∈
      boundedMProcess P (fun t => F (finitePrefixTime b hb t).val) := by
  let p := fun t : HalfClosedTime => (finitePrefixTime b hb t).val
  have hp t : p t∈Icc 0 b := (finitePrefixTime b hb t).property
  have hpm : Monotone p := fun s t hst => finite_prefix_time_mono b hb hst
  have hpc : Continuous p := continuous_subtype_val.comp (finite_prefix_time_continuous b hb)
  have hLp t : MemLp (Y (p t)) ∞ P :=
    memLp_top_of_bound ((hm _ (hp t)).mono (hle _) le_rfl).aestronglyMeasurable C
      (ae_of_all _ (hbound _ (hp t)))
  refine ⟨⟨fun t => hm _ (hp t),fun t => (hLp t).mono_exponent (by simp),
    fun w => (hc w).comp_continuous hpc hp,
    fun s t hst => hce _ _ (hp s).1 (hpm hst) (hp t).2,?_⟩,hLp⟩
  apply ae_of_all
  intro w
  have hp0 : p ⊥=0 := by
    change (min (0:EReal) (b:EReal)).toReal=0
    rw [min_eq_left (by exact_mod_cast hb)]
    rfl
  change Y (p ⊥) w=0
  rw [hp0,hz]
end Asakura.Chapter9
