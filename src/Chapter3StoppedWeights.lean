import Chapter3StoppedOrthogonality

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- A stopping-time measurable coefficient becomes F_t measurable when cut
off to the event that the stopping time has already occurred. -/
theorem stopped_weight_indicator_measurable
    {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (σ : Ω → ι)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (A : Ω → ℝ) (hA : Measurable[writtenStoppedSpace m F σ hσ] A) (t : ι) :
    Measurable[F t] ({ω | σ ω ≤ t}.indicator A) := by
  intro B hB
  have hAB := (hA hB).2 t
  by_cases h0 : (0:ℝ) ∈ B
  · have he : ({ω | σ ω ≤ t}.indicator A) ⁻¹' B =
        (A ⁻¹' B ∩ {ω | σ ω ≤ t}) ∪ {ω | σ ω ≤ t}ᶜ := by
      ext ω
      by_cases hω : σ ω ≤ t <;> simp [Set.indicator,hω,h0]
    rw [he]
    exact hAB.union (hσ t).compl
  · have he : ({ω | σ ω ≤ t}.indicator A) ⁻¹' B =
        A ⁻¹' B ∩ {ω | σ ω ≤ t} := by
      ext ω
      by_cases hω : σ ω ≤ t <;> simp [Set.indicator,hω,h0]
    rw [he]
    exact hAB

/-- The product's adaptedness does not require A itself to be F_t measurable
before σ: the other factor is zero there. -/
theorem stopped_weight_product_adapted
    {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (σ : Ω → ι)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (Y : ι → Ω → ℝ) (hY : ∀ t, Measurable[F t] (Y t))
    (hz : ∀ ω t, t ≤ σ ω → Y t ω = 0)
    (A : Ω → ℝ) (hA : Measurable[writtenStoppedSpace m F σ hσ] A) :
    ∀ t, Measurable[F t] (fun ω => A ω*Y t ω) := by
  intro t
  have he : (fun ω => A ω*Y t ω) =
      (fun ω => ({ω | σ ω ≤ t}.indicator A) ω * Y t ω) := by
    funext ω
    by_cases ht : σ ω ≤ t
    · simp [Set.indicator,ht]
    · simp [Set.indicator,ht,hz ω t (le_of_not_ge ht)]
  rw [he]
  exact (stopped_weight_indicator_measurable F σ hσ A hA t).mul (hY t)

/-- A test event known at s, restricted to the event σ>s, belongs to Fσ. -/
theorem past_event_before_stop_measurable
    {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (σ : Ω → ι) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (s : ι) (E : Set Ω) (hE : MeasurableSet[F s] E) :
    MeasurableSet[writtenStoppedSpace m F σ hσ] (E ∩ {ω | σ ω ≤ s}ᶜ) := by
  refine ⟨(hle s _ hE).inter ((hle s _ (hσ s)).compl),?_⟩
  intro t
  by_cases hst : s ≤ t
  · exact ((hF hst _ hE).inter ((hF hst _ (hσ s)).compl)).inter (hσ t)
  · have he : (E ∩ {ω | σ ω ≤ s}ᶜ) ∩ {ω | σ ω ≤ t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hω.1.2 (hω.2.trans (le_of_not_ge hst))
    rw [he]
    exact @MeasurableSet.empty Ω (F t)

/-- Optional sampling at σ applied to a deterministically stopped process
shows that every later-time pairing with an Fσ coefficient has mean zero. -/
theorem stopped_zero_pairing_at_time
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Y : ClosedTime T → Ω → ℝ) (hY : ContinuousM2Witness P F Y)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hz : ∀ ω t, t ≤ σ ω → Y t ω = 0)
    (A : Ω → ℝ) (hA : Measurable[writtenStoppedSpace m F σ hσ] A)
    (hA2 : MemLp A 2 P) (t : ClosedTime T) :
    (∫ ω, A ω * Y t ω ∂P) = 0 := by
  have ht : ∀ r, MeasurableSet[F r] {ω : Ω | t ≤ r} := by
    intro r
    by_cases h : t ≤ r <;> simp [h]
  have hs := continuous_m2_stopped P F hF hle Y hY (fun _ => t) ht
  have he := stopped_zero_martingale_orthogonal P F hF hle _ hs σ hσ
    (.of_forall fun ω => hz ω _ (min_le_right _ _)) A hA hA2
  simpa only [min_top_right] using he

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_weight_indicator_measurable
#print axioms Asakura.Chapter3Complete.stopped_weight_product_adapted

#print axioms Asakura.Chapter3Complete.past_event_before_stop_measurable
#print axioms Asakura.Chapter3Complete.stopped_zero_pairing_at_time
