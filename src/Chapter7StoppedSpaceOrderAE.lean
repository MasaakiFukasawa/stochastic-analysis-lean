import Chapter7StoppedSpaceAE
import Chapter7FiniteStoppedSampling

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000

theorem stopped_space_mono_ae
    {Ω ι : Type*} [LinearOrder ι] {m : MeasurableSpace Ω} (P : Measure Ω)
    (F : ι → MeasurableSpace Ω) (hl : ∀ t,F t ≤ m)
    (hn : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (σ τ : Ω → ι) (hσ : ∀ t,MeasurableSet[F t] {w | σ w ≤ t})
    (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t}) (he : σ ≤ᵐ[P] τ) :
    writtenStoppedSpace m F σ hσ ≤ writtenStoppedSpace m F τ hτ := by
  intro A hA
  refine ⟨hA.1,fun t => ?_⟩
  apply measurable_event_of_augmented_ae P (F t) (hl t) (hn t)
    (A ∩ {w | τ w ≤ t}) ((A ∩ {w | σ w ≤ t}) ∩ {w | τ w ≤ t})
    (hA.1.inter (hl t _ (hτ t))) ((hA.2 t).inter (hτ t))
  filter_upwards [he] with w hw
  simp only [mem_inter_iff,mem_setOf_eq]
  constructor
  · intro h; exact ⟨⟨h.1,hw.trans h.2⟩,h.2⟩
  · intro h; exact ⟨h.1.1,h.2⟩

theorem nnreal_stopping_add
    {Ω : Type*} (F : ℝ≥0 → MeasurableSpace Ω) (hF : Monotone F)
    (τ : Ω → ℝ≥0) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t}) (r : ℝ≥0) :
    ∀ t,MeasurableSet[F t] {w | τ w+r ≤ t} := by
  intro t
  letI : MeasurableSpace Ω := F t
  by_cases hr : r ≤ t
  · have he : {w | τ w+r ≤ t} = {w | τ w ≤ t-r} := by ext w; exact (le_tsub_iff_right hr).symm
    rw [he]
    exact hF tsub_le_self _ (hτ (t-r))
  · have he : {w | τ w+r ≤ t} = ∅ := by
      ext w
      simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
      exact fun h => hr ((le_add_left le_rfl).trans h)
    rw [he]
    exact MeasurableSet.empty

end Asakura.Chapter7
