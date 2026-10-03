import Chapter11NoArbitrage

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

lemma conditional_le_of_event_integrals {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) (hYm : StronglyMeasurable[G] Y)
    (hi : ∀ A,MeasurableSet[G] A → (∫ w in A,X w ∂P)≤∫ w in A,Y w ∂P) :
    P[X|G]≤ᵐ[P] Y := by
  have hm : StronglyMeasurable[G] (P[X|G]) := stronglyMeasurable_condExp
  apply ae_of_ae_trim hG
  apply ae_le_of_forall_setIntegral_le (Integrable.trim hG integrable_condExp hm) (Integrable.trim hG hY hYm)
  intro A hA hAfin
  rw [←setIntegral_trim hG hm hA,←setIntegral_trim hG hYm hA,setIntegral_condExp hG hX hA]
  exact hi A hA

/-- The conditional Fatou step in the manuscript, for a wealth process
bounded below only on the finite investment interval. -/
theorem finite_lower_bounded_local_supermartingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (R : ClosedTime T) (hR : R<⊤) (a : ℝ)
    (hb : ∀ᵐ w ∂P,∀ t,t≤R → -a≤X t w) :
    (∀ t,t≤R → Integrable (X t) P) ∧
      ∀ s t,s≤t → t≤R → P[X t|F s]≤ᵐ[P] X s := by
  let Y := fun t w => X (min R t) w
  have hs t : MeasurableSet[F t] {w : Ω | R≤t} := by
    by_cases h : R≤t <;> simp [h]
  have hY := hX.stopped P F hF hle (fun _ => R) hs
  have hbound : ∀ᵐ w ∂P,∀ t,t<⊤ → -a≤Y t w := hb.mono fun w hw t ht => hw _ (min_le_left _ _)
  obtain ⟨hm,hi,_,_,he⟩ := lower_bounded_local_stopped_supermartingale P F hF hle Y hY (fun _ => R) hs (fun _ => hR) a hbound
  have hval t (ht : t≤R) : (fun w => Y (min R t) w)=X t := by funext w;simp only [Y,min_eq_right ht]
  have hi' t (ht : t≤R) : Integrable (X t) P := by simpa only [hval t ht] using hi t
  refine ⟨hi',?_⟩
  intro s t hst ht
  have hsm : StronglyMeasurable[F s] (X s) := (hX.adapted P F s ((hst.trans ht).trans_lt hR)).stronglyMeasurable
  apply conditional_le_of_event_integrals P (F s) (hle s) (X t) (X s) (hi' t ht) (hi' s (hst.trans ht)) hsm
  intro A hA
  simpa only [hval s (hst.trans ht),hval t ht] using he s t hst A hA

end Asakura.Chapter11
