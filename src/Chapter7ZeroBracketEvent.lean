import Chapter7FlatBracketBound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- On the event where the stopped bracket is zero, the entire stopped
local-martingale path is zero. The event is not assumed measurable at time
zero. It is controlled by first stopping at a small positive bracket level. -/
theorem zero_bracket_event_path_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t,MeasurableSet[F t] {w | σ w ≤ t})
    (hσt : ∀ w,σ w < ⊤) :
    ∀ᵐ w ∂P,C (σ w) w = 0 → ∀ t,X (min (σ w) t) w = 0 := by
  let Z := fun w => ‖localStoppedPath P F hF hle hX σ hσ hσt w‖
  have hz (ε : ℝ) (hε : 0 < ε) : P {w | ε ≤ Z w ∧ C (σ w) w = 0} = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top P _)).mp
    apply le_antisymm _ ENNReal.toReal_nonneg
    by_contra hn
    let p := P.real {w | ε ≤ Z w ∧ C (σ w) w = 0}
    have hp : 0 < p := lt_of_not_ge hn
    let δ := p*ε^2/2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hh := local_small_bracket_large_path_probability P F hF hle hnull X C hX hC σ hσ hσt ε δ hε hδ
    have hsub : {w | ε ≤ Z w ∧ C (σ w) w = 0} ⊆
        {w | ε ≤ Z w ∧ C (σ w) w < δ} := by
      intro w hw
      exact ⟨hw.1,hw.2 ▸ hδ⟩
    have hle' : p ≤ δ/ε^2 :=
      (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)).trans hh
    have he : δ/ε^2 = p/2 := by dsimp [δ]; field_simp
    rw [he] at hle'
    linarith
  have ha (n : ℕ) : ∀ᵐ w ∂P,¬ (1/(n+1:ℝ) ≤ Z w ∧ C (σ w) w = 0) := by
    apply ae_iff.mpr
    simpa only [not_not] using hz (1/(n+1:ℝ)) (by positivity)
  filter_upwards [ae_all_iff.mpr ha] with w hw
  intro hzero
  have hnorm : Z w = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hn
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (lt_of_not_ge hn)
    exact hw n ⟨hn.le,hzero⟩
  have hpath : localStoppedPath P F hF hle hX σ hσ hσt w = 0 := norm_eq_zero.mp hnorm
  intro t
  have he := congrArg (fun f : C(ClosedTime T,ℝ) => f t) hpath
  exact he

end Asakura.Chapter7
