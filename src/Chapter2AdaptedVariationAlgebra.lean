import Chapter2ActualLocalVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
  {F : ClosedTime T → MeasurableSpace Ω} {A B : ClosedTime T → Ω → ℝ}

theorem AdaptedVariationWitness.add (hA : AdaptedVariationWitness F A)
    (hB : AdaptedVariationWitness F B) : AdaptedVariationWitness F (fun t ω => A t ω+B t ω) := by
  obtain ⟨U,V,hm,hmon,hr,he⟩ := hA.parts
  obtain ⟨U',V',hm',hmon',hr',he'⟩ := hB.parts
  refine ⟨fun t ω => U t ω+U' t ω,fun t ω => V t ω+V' t ω,?_,?_,?_,?_⟩
  · intro t; exact ⟨(hm t).1.add (hm' t).1,(hm t).2.add (hm' t).2⟩
  · intro ω; exact ⟨(hmon ω).1.add (hmon' ω).1,(hmon ω).2.add (hmon' ω).2⟩
  · intro ω t; exact ⟨(hr ω t).1.add (hr' ω t).1,(hr ω t).2.add (hr' ω t).2⟩
  · intro t ω; rw [he,he']; ring

theorem AdaptedVariationWitness.smul (hA : AdaptedVariationWitness F A) (c : ℝ) :
    AdaptedVariationWitness F (fun t ω => c*A t ω) := by
  obtain ⟨U,V,hm,hmon,hr,he⟩ := hA.parts
  have hp : 0 ≤ max c 0 := le_max_right _ _
  have hn : 0 ≤ max (-c) 0 := le_max_right _ _
  refine ⟨fun t ω => max c 0*U t ω+max (-c) 0*V t ω,
    fun t ω => max c 0*V t ω+max (-c) 0*U t ω,?_,?_,?_,?_⟩
  · intro t
    exact ⟨((hm t).1.const_mul _).add ((hm t).2.const_mul _),
      ((hm t).2.const_mul _).add ((hm t).1.const_mul _)⟩
  · intro ω
    exact ⟨((hmon ω).1.const_mul hp).add ((hmon ω).2.const_mul hn),
      ((hmon ω).2.const_mul hp).add ((hmon ω).1.const_mul hn)⟩
  · intro ω t
    exact ⟨((hr ω t).1.const_mul _).add ((hr ω t).2.const_mul _),
      ((hr ω t).2.const_mul _).add ((hr ω t).1.const_mul _)⟩
  · intro t ω
    rw [he]
    have hc := max_zero_sub_max_neg_zero_eq_self c
    calc
      c*(U t ω-V t ω) = (max c 0-max (-c) 0)*(U t ω-V t ω) := by rw [hc]
      _ = _ := by dsimp only; ring

theorem AdaptedVariationWitness.stopped (hA : AdaptedVariationWitness F A)
    (hF : Monotone F) (σ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t}) :
    AdaptedVariationWitness F (fun t ω => A (min (σ ω) t) ω) := by
  obtain ⟨U,V,hm,hmon,hr,he⟩ := hA.parts
  refine ⟨fun t ω => U (min (σ ω) t) ω,fun t ω => V (min (σ ω) t) ω,?_,?_,?_,?_⟩
  · intro t
    exact ⟨stopped_min_value_measurable F hF σ hσ U (fun s => (hm s).1) (fun ω s => (hr ω s).1) t,
      stopped_min_value_measurable F hF σ hσ V (fun s => (hm s).2) (fun ω s => (hr ω s).2) t⟩
  · intro ω
    exact ⟨(hmon ω).1.comp (monotone_const.min monotone_id),
      (hmon ω).2.comp (monotone_const.min monotone_id)⟩
  · intro ω t
    have hmin : ContinuousWithinAt (fun s : ClosedTime T => min (σ ω) s) (Ici t) t :=
      (continuous_const.min continuous_id).continuousAt.continuousWithinAt
    have hmap : MapsTo (fun s : ClosedTime T => min (σ ω) s) (Ici t) (Ici (min (σ ω) t)) :=
      fun s hs => show min (σ ω) t ≤ min (σ ω) s from min_le_min_left _ hs
    exact ⟨(hr ω _).1.comp hmin hmap,(hr ω _).2.comp hmin hmap⟩
  · intro t ω; exact he _ ω

theorem AdaptedLocalVariationWitness.add (hA : AdaptedLocalVariationWitness F A)
    (hB : AdaptedLocalVariationWitness F B) (hF : Monotone F) :
    AdaptedLocalVariationWitness F (fun t ω => A t ω+B t ω) := by
  obtain ⟨τ,ht,hm,htt,hc,ha⟩ := hA.localizers
  obtain ⟨σ,hs,hsm,hst,hsc,hb⟩ := hB.localizers
  refine ⟨fun n ω => min (τ n ω) (σ n ω),?_,?_,?_,?_,?_⟩
  · intro n; exact (written_stopping_min_max F (τ n) (σ n) (ht n) (hs n)).1
  · intro ω; exact (hm ω).min (hsm ω)
  · intro n ω; exact (min_le_left _ _).trans_lt (htt n ω)
  · intro ω
    exact (common_localizers_cofinal (fun n => τ n ω) (fun n => σ n ω)
      (hm ω) (hsm ω) (hc ω) (hsc ω)).2
  · intro n
    have h := ((ha n).stopped hF (σ n) (hs n)).add ((hb n).stopped hF (τ n) (ht n))
    simpa only [← min_assoc,min_comm (σ n _) (τ n _)] using h

theorem AdaptedLocalVariationWitness.smul (hA : AdaptedLocalVariationWitness F A) (c : ℝ) :
    AdaptedLocalVariationWitness F (fun t ω => c*A t ω) := by
  obtain ⟨τ,ht,hm,htt,hc,ha⟩ := hA.localizers
  exact ⟨τ,ht,hm,htt,hc,fun n => (ha n).smul c⟩

theorem AdaptedLocalVariationWitness.stopped (hA : AdaptedLocalVariationWitness F A)
    (hF : Monotone F) (σ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t}) :
    AdaptedLocalVariationWitness F (fun t ω => A (min (σ ω) t) ω) := by
  obtain ⟨τ,ht,hm,htt,hc,ha⟩ := hA.localizers
  refine ⟨τ,ht,hm,htt,hc,?_⟩
  intro n
  simpa only [min_left_comm (σ _) (τ n _)] using (ha n).stopped hF σ hσ

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.AdaptedLocalVariationWitness.add
#print axioms Asakura.Chapter2Complete.AdaptedLocalVariationWitness.stopped
