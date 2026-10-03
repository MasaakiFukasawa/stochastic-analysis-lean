import Chapter4BoundedLocalPointwise
import Chapter4VectorTimeIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- A bounded continuous function of time and an adapted vector process
has the conditional identity once its actual local martingale representation
has been constructed. The representation is needed only at fixed times. -/
theorem vector_bounded_conditional_from_local_representation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X : ClosedTime T → Ω → Fin d → ℝ)
    (ha : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (f : ℝ × (Fin d → ℝ) → ℝ) (hf : Continuous f)
    (N : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (K : ℝ)
    (hb : ∀ r∈Icc 0 R,∀ x,|f (r,x)|≤K)
    (he : ∀ r∈Icc 0 R,(fun w => f (r,X (realTimeClamp r) w))=ᵐ[P]
      fun w => f (0,X ⊥ w)+N (realTimeClamp r) w)
    (s : ℝ) (hs : s∈Icc 0 R) :
    P[(fun w => f (R,X (realTimeClamp R) w)) | F (realTimeClamp s)]=ᵐ[P]
      fun w => f (s,X (realTimeClamp s) w) := by
  let V := fun t w => f ((finitePrefixTime (T := T) R hR t).val,X t w)
  have hva t (ht : t<⊤) : Measurable[F t] (V t) := by
    letI : MeasurableSpace Ω := F t
    exact hf.measurable.comp (measurable_const.prodMk (ha t ht))
  have hvc w t (ht : t<⊤) : ContinuousAt (fun u => V u w) t :=
    hf.continuousAt.comp (((continuous_subtype_val.comp (finite_prefix_time_continuous R hR)).continuousAt).prodMk (hc w t ht))
  have hzero : (finitePrefixTime (T := T) R hR ⊥).val=0 := by
    change (min (0:EReal) (R:EReal)).toReal=0
    rw [min_eq_left (by exact_mod_cast hR),EReal.toReal_zero]
  have hrepr t (ht : t≤realTimeClamp (T := T) R) :
      V t=ᵐ[P] fun w => V ⊥ w+N t w := by
    let r := (finitePrefixTime (T := T) R hR t).val
    have hr : r∈Icc 0 R := (finitePrefixTime (T := T) R hR t).property
    have hrt : realTimeClamp (T := T) r=t := by
      rw [finite_prefix_time_clamp R hR hRT.le,min_eq_right ht]
    have hh := he r hr
    simpa only [hrt,V,hzero] using hh
  have hh := bounded_local_increment_conditional_of_pointwise P hT F hF hle V N hN hva hvc
    (realTimeClamp R) (real_time_below R hR hRT) K
    (ae_of_all _ fun w t _ => hb _ (finitePrefixTime (T := T) R hR t).property _) hrepr
    (realTimeClamp s) (real_time_clamp_mono hs.2)
  simpa only [V,finite_prefix_time_of_real R R hR ⟨hR,le_rfl⟩ hRT.le,
    finite_prefix_time_of_real R s hR hs hRT.le] using hh

end Asakura.Chapter4
