import Chapter3DiscreteIntegralItoFormula
import Chapter3ContinuousAdaptedWeights

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- For bounded continuous adapted H, the constructed Ito integral of its
partition step process is exactly the countable discrete sum, at all finite
times on one common event of probability one. -/
theorem bounded_discrete_integral_identification
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X H : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ j t, MeasurableSet[F t] {ω | τ j ω ≤ t})
    (hτm : ∀ ω, Monotone (fun j => τ j ω)) (hτt : ∀ j ω, τ j ω < ⊤)
    (hτc : ∀ ω t, t < ⊤ → ∃ j, t < τ j ω)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (K : ℝ) (hK : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → |H t ω| ≤ K)
    (Z : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hZI : ItoCovarianceFormula P F X
      (fun z => partitionStep (fun t => H t z.1) (fun j => τ j z.1) (realTimeClamp z.2)) Z) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Z t ω =
      ∑' j, H (τ j ω) ω*(X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω) := by
  have hcoeff (j) :
      Measurable[writtenStoppedSpace m F (τ j) (hτ j)] (fun ω => H (τ j ω) ω) ∧
      MemLp (fun ω => H (τ j ω) ω) ∞ P := by
    obtain ⟨hm,hc⟩ := open_continuous_adapted_stopped_regular F hF H hHm hHc
      c hcm hct hcc (τ j) (hτ j) (hτt j)
    have hb : ∀ᵐ ω ∂P, ∀ t, |H (min (τ j ω) t) ω| ≤ K :=
      hK.mono (fun ω hω t => hω _ ((min_le_left _ _).trans_lt (hτt j ω)))
    obtain ⟨ha,hb,_⟩ := continuous_adapted_stopping_weights P F hF hle
      (fun t ω => H (min (τ j ω) t) ω) hm hc (τ j) (hτ j) K hb
    simpa only [min_self] using And.intro ha hb
  have hR := discrete_integral_local_martingale P F hF hle X hX τ hτ hτm hτt hτc
    (fun j ω => H (τ j ω) ω) (fun j => (hcoeff j).1) (fun j => (hcoeff j).2)
  have hRI := discrete_integral_ito_formula P F hF hle hnull X H hX c hcm hct hcc
    τ hτ hτm hτt hτc (fun j => (hcoeff j).1) (fun j => (hcoeff j).2)
  exact hZI.unique P hT F hF hle hnull X Z _ _ hX hZ hR hRI

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bounded_discrete_integral_identification
