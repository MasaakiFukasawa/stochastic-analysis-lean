import Chapter4ConstructedClockIto

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option backward.isDefEq.respectTransparency false

theorem ode_composition_constructed_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (φ f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hφ : ∀ x, HasDerivAt φ (f (φ x)) x)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → C (realTimeClamp r) ω = r) :
    ∃ Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X
        (fun z => f (φ (X (realTimeClamp z.2) z.1))) Z ∧
      ∀ᵐ ω ∂P, ∀ d : ℝ, 0 ≤ d → (d:EReal) < T →
        φ (X (realTimeClamp d) ω) = φ (X ⊥ ω)+Z (realTimeClamp d) ω+
          (∫ r in 0..d, deriv f (φ (X (realTimeClamp r) ω))*f (φ (X (realTimeClamp r) ω)))/2 := by
  apply constructed_clock_ito P hT F hF hle hnull X C hX hC φ
    (fun z => f (φ z)) (fun z => deriv f (φ z)*f (φ z))
    (ode_solution_c2 φ f hf hφ) hφ _ c hc hcm hcT hcc hclock
  intro x
  exact ((hf.differentiable (by norm_num)) (φ x)).hasDerivAt.comp x (hφ x)

end Asakura.Chapter4
