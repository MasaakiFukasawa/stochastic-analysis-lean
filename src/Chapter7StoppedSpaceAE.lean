import Chapter7ClockHalfTime
import Chapter7NullEventTransfer

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000

/-- Stopped sigma algebras do not depend on an almost-everywhere choice
of stopping times in a filtration containing ambient measurable null sets. -/
theorem stopped_space_ae_eq
    {Ω ι : Type*} [LinearOrder ι] {m : MeasurableSpace Ω} (P : Measure Ω)
    (F : ι → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (τ σ : Ω → ι) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t})
    (hσ : ∀ t,MeasurableSet[F t] {w | σ w ≤ t}) (he : τ =ᵐ[P] σ) :
    writtenStoppedSpace m F τ hτ = writtenStoppedSpace m F σ hσ := by
  have hdir (u v : Ω → ι) (hu : ∀ t,MeasurableSet[F t] {w | u w ≤ t})
      (hv : ∀ t,MeasurableSet[F t] {w | v w ≤ t}) (heq : u =ᵐ[P] v) :
      writtenStoppedSpace m F u hu ≤ writtenStoppedSpace m F v hv := by
    intro E hE
    refine ⟨hE.1,fun t => ?_⟩
    apply measurable_event_of_augmented_ae P (F t) (hle t) (hnull t)
      (E ∩ {w | v w ≤ t}) (E ∩ {w | u w ≤ t})
      (hE.1.inter (hle t _ (hv t))) (hE.2 t)
    filter_upwards [heq] with w hw
    simp only [mem_inter_iff,mem_setOf_eq,hw]
  exact le_antisymm (hdir τ σ hτ hσ he) (hdir σ τ hσ hτ he.symm)

end Asakura.Chapter7
