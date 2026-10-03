import Chapter7ZeroBracketEvent
import Chapter7DenseFlatPaths
import Chapter6IncrementCovariance
import Chapter2LocalPathEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The flat-clock property is derived from the original local martingale
and its actual bracket, simultaneously for all times. -/
theorem local_martingale_constant_on_bracket_levels
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C) :
    ∀ᵐ w ∂P,∀ a b,a < ⊤ → b < ⊤ → C a w = C b w → X a w = X b w := by
  have hstop (r : ClosedTime T) : ∀ t,MeasurableSet[F t] {w : Ω | r ≤ t} := by
    intro t
    by_cases h : r ≤ t <;> simp [h]
  have hp (a b : ClosedTime T) (hb : b < ⊤) (hab : a ≤ b) :
      ∀ᵐ w ∂P,C a w = C b w → X a w = X b w := by
    obtain ⟨hY,hD⟩ := Asakura.Chapter6.after_stop_self_covariance P F hF hle hnull X C hX hC
      (fun _ => a) (hstop a)
    have hh := zero_bracket_event_path_zero P F hF hle hnull _ _ hY hD
      (fun _ => b) (hstop b) (fun _ => hb)
    filter_upwards [hh] with w hw
    intro he
    have hz : C b w-C (min a b) w = 0 := by rw [min_eq_left hab,he,sub_self]
    have hh := hw hz b
    simp only [min_self,min_eq_left hab] at hh
    exact (sub_eq_zero.mp hh).symm
  have hp' (a b : Iio (⊤ : ClosedTime T)) :
      ∀ᵐ w ∂P,C a w = C b w → X a w = X b w := by
    rcases le_total a.val b.val with hab | hba
    · exact hp a b b.property hab
    · filter_upwards [hp b a a.property hba] with w hw
      exact fun he => (hw he.symm).symm
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : ClosedTime T))
  have hall : ∀ᵐ w ∂P,∀ i j,C (q i) w = C (q j) w → X (q i) w = X (q j) w :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hp' (q i) (q j)))
  have hm := local_quadratic_variation_monotone P F hF hle hnull X C hX hC
  filter_upwards [hall,hm] with w hw hmono
  have hflat := continuous_flat_of_dense (range q) (TopologicalSpace.denseRange_denseSeq _)
    (fun t : Iio (⊤ : ClosedTime T) => C t.val w)
    (fun a b hab => hmono a.property b.property hab)
    (fun t : Iio (⊤ : ClosedTime T) => X t.val w)
    (localOpenPath P F hX w).continuous
    (by rintro a ⟨i,rfl⟩ b ⟨j,rfl⟩; exact hw i j)
  intro a b ha hb he
  exact hflat ⟨a,ha⟩ ⟨b,hb⟩ he

end Asakura.Chapter7
