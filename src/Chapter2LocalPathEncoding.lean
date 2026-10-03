import Chapter2LocalCompleteness

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- The unused value at T cannot affect local-martingale membership. -/
theorem LocalMProcessWitness.congr_before_terminal
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X Y : ClosedTime T → Ω → ℝ} (hX : LocalMProcessWitness P F X)
    (he : ∀ t, t < ⊤ → X t = Y t) : LocalMProcessWitness P F Y := by
  obtain ⟨τ,hs,hm,ht,hc,hM⟩ := hX.localizers
  refine ⟨τ,hs,hm,ht,hc,?_⟩
  intro n
  have heq : (fun t ω => X (min (τ n ω) t) ω) = fun t ω => Y (min (τ n ω) t) ω := by
    funext t ω
    exact congrFun (he _ ((min_le_left _ _).trans_lt (ht n ω))) ω
  rw [← heq]
  exact hM n

/-- Encode the existing continuous paths on [0,T) without introducing a
terminal value or claiming a limit at T. -/
noncomputable def localOpenPath
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X : ClosedTime T → Ω → ℝ} (hX : LocalMProcessWitness P F X) (ω : Ω) :
    C(Iio (⊤ : ClosedTime T),ℝ) := ⟨fun t => X t.val ω,by
      apply continuous_iff_continuousAt.2
      intro t
      exact (hX.path P F ω t.val t.property).comp continuous_subtype_val.continuousAt⟩

theorem local_open_path_witness
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X : ClosedTime T → Ω → ℝ} (hX : LocalMProcessWitness P F X) :
    LocalMProcessWitness P F (fun t ω => extendOpenPath (localOpenPath P F hX ω) t) := by
  apply hX.congr_before_terminal P F
  intro t ht
  funext ω
  simp only [extendOpenPath,dif_pos ht]
  rfl

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.LocalMProcessWitness.congr_before_terminal
#print axioms Asakura.Chapter2Complete.local_open_path_witness
