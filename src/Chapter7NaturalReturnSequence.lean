import Chapter7BrownianReturnSequence
import Chapter7FiniteStoppingCoordinate

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2200000

/-- The return sequence for the original Brownian process, in finite
nonnegative real time and its completed natural filtration. -/
theorem natural_brownian_return_sequence
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w)) :
    ∃ τ : ℕ → Ω → ℝ≥0,
      (∀ n t,MeasurableSet[Asakura.nullAugmentation P (pastSigma B t)] {w | τ n w ≤ t}) ∧
      (∀ w,τ 0 w = 0) ∧
      (∀ᵐ w ∂P,∀ n,τ n w+1 ≤ τ (n+1) w ∧ B (τ n w) w = 0) := by
  let BB := naturalBrownianSystem P B hB hm hc
  obtain ⟨σ,hσ,hσ0,hinfo⟩ := brownian_return_sequence P BB
  let F := fun t => Asakura.nullAugmentation (m := m) P (pastSigma B t)
  have hF : Monotone F := fun s t hst => null_augmentation_mono P (past_sigma_mono B hst)
  have hl t : F t ≤ m := fun _ he => he.1
  have hn t N hmN hzN : MeasurableSet[F t] N := null_augmentation_null P (pastSigma B t) N hmN hzN
  let τ := fun n w => halfTimeReal (σ n w)
  have hτ n : ∀ t,MeasurableSet[F t] {w | τ n w ≤ t} :=
    finite_stopping_coordinate P F hF hl hn (σ n) (hσ n) (hinfo.mono fun w h => (h n).1)
  refine ⟨τ,hτ,?_,?_⟩
  · intro w
    change halfTimeReal (σ 0 w) = 0
    rw [hσ0]
    rfl
  · filter_upwards [hinfo] with w hw
    intro n
    exact ⟨(hw n).2.2.1,(hw n).2.2.2⟩

end Asakura.Chapter7
