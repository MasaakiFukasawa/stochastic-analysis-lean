import Chapter2LocalProcess

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- A common null-set modification preserves the actual bounded
martingale witness, including adaptedness and continuous paths. -/
theorem bounded_martingale_null_modification
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (N : Set Ω) (hN : ∀ t, MeasurableSet[F t] N) (hNP : P N = 0)
    (X : ClosedTime T → Ω → ℝ) (hX : X ∈ boundedMProcess P F) :
    (fun t ω => if ω ∈ N then 0 else X t ω) ∈ boundedMProcess P F := by
  have hn : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hNP
  have he (t) : (fun ω => if ω ∈ N then 0 else X t ω) =ᵐ[P] X t :=
    hn.mono fun ω hω => if_neg hω
  refine ⟨{ adapted := fun t => Measurable.ite (hN t) measurable_const (hX.1.adapted t)
            moment := fun t => (memLp_congr_ae (he t)).2 (hX.1.moment t)
            path := ?_
            martingale := ?_
            initial := (he ⊥).trans hX.1.initial },fun t => (memLp_congr_ae (he t)).2 (hX.2 t)⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simpa only [if_pos hω] using (continuous_const : Continuous (fun _ : ClosedTime T => (0:ℝ)))
    · simpa only [if_neg hω] using hX.1.path ω
  · intro s t hst
    exact (condExp_congr_ae (he t)).trans ((hX.1.martingale s t hst).trans (he s).symm)

/-- The same localizers work after the common null-set removal used in
the completeness proof. -/
theorem local_martingale_null_modification
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (N : Set Ω) (hN : ∀ t, MeasurableSet[F t] N) (hNP : P N = 0)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    LocalMProcessWitness P F (fun t ω => if ω ∈ N then 0 else X t ω) := by
  obtain ⟨τ,ht,hm,htt,hc,hb⟩ := hX.localizers
  exact ⟨τ,ht,hm,htt,hc,fun n => bounded_martingale_null_modification P F N hN hNP _ (hb n)⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.bounded_martingale_null_modification
#print axioms Asakura.Chapter2Complete.local_martingale_null_modification
