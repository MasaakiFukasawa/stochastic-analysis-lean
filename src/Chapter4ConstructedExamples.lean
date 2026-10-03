import Chapter4ConstructedClockIto

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem circle_cos_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (a σ θ : ℝ)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → C (realTimeClamp r) ω = r) :
    ∃ Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X
        (fun z => (fun z : ℝ => -σ*(a*Real.sin (σ*z+θ))) (X (realTimeClamp z.2) z.1)) Z ∧
      ∀ᵐ ω ∂P, ∀ d : ℝ, 0 ≤ d → (d:EReal) < T →
        (fun z : ℝ => a*Real.cos (σ*z+θ)) (X (realTimeClamp d) ω) = (fun z : ℝ => a*Real.cos (σ*z+θ)) (X ⊥ ω)+Z (realTimeClamp d) ω+
          (∫ r in 0..d, (fun z : ℝ => -σ^2*(a*Real.cos (σ*z+θ))) (X (realTimeClamp r) ω))/2 := by
  exact constructed_clock_ito P hT F hF hle hnull X C hX hC
    (fun z => a*Real.cos (σ*z+θ)) (fun z => -σ*(a*Real.sin (σ*z+θ))) (fun z => -σ^2*(a*Real.cos (σ*z+θ)))
    (by fun_prop) (fun x => (circle_derivatives a σ θ x).1) (fun x => (circle_second_derivatives a σ θ x).1) c hc hcm hcT hcc hclock

theorem circle_sin_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (a σ θ : ℝ)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → C (realTimeClamp r) ω = r) :
    ∃ Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X
        (fun z => (fun z : ℝ => σ*(a*Real.cos (σ*z+θ))) (X (realTimeClamp z.2) z.1)) Z ∧
      ∀ᵐ ω ∂P, ∀ d : ℝ, 0 ≤ d → (d:EReal) < T →
        (fun z : ℝ => a*Real.sin (σ*z+θ)) (X (realTimeClamp d) ω) = (fun z : ℝ => a*Real.sin (σ*z+θ)) (X ⊥ ω)+Z (realTimeClamp d) ω+
          (∫ r in 0..d, (fun z : ℝ => -σ^2*(a*Real.sin (σ*z+θ))) (X (realTimeClamp r) ω))/2 := by
  exact constructed_clock_ito P hT F hF hle hnull X C hX hC
    (fun z => a*Real.sin (σ*z+θ)) (fun z => σ*(a*Real.cos (σ*z+θ))) (fun z => -σ^2*(a*Real.sin (σ*z+θ)))
    (by fun_prop) (fun x => (circle_derivatives a σ θ x).2) (fun x => (circle_second_derivatives a σ θ x).2) c hc hcm hcT hcc hclock

theorem hyperbolic_cosh_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (a σ θ : ℝ)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → C (realTimeClamp r) ω = r) :
    ∃ Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X
        (fun z => (fun z : ℝ => σ*(a*Real.sinh (σ*z+θ))) (X (realTimeClamp z.2) z.1)) Z ∧
      ∀ᵐ ω ∂P, ∀ d : ℝ, 0 ≤ d → (d:EReal) < T →
        (fun z : ℝ => a*Real.cosh (σ*z+θ)) (X (realTimeClamp d) ω) = (fun z : ℝ => a*Real.cosh (σ*z+θ)) (X ⊥ ω)+Z (realTimeClamp d) ω+
          (∫ r in 0..d, (fun z : ℝ => σ^2*(a*Real.cosh (σ*z+θ))) (X (realTimeClamp r) ω))/2 := by
  exact constructed_clock_ito P hT F hF hle hnull X C hX hC
    (fun z => a*Real.cosh (σ*z+θ)) (fun z => σ*(a*Real.sinh (σ*z+θ))) (fun z => σ^2*(a*Real.cosh (σ*z+θ)))
    (by fun_prop) (fun x => (hyperbolic_derivatives a σ θ x).1) (fun x => (hyperbolic_second_derivatives a σ θ x).1) c hc hcm hcT hcc hclock

theorem hyperbolic_sinh_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (a σ θ : ℝ)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → C (realTimeClamp r) ω = r) :
    ∃ Z : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X
        (fun z => (fun z : ℝ => σ*(a*Real.cosh (σ*z+θ))) (X (realTimeClamp z.2) z.1)) Z ∧
      ∀ᵐ ω ∂P, ∀ d : ℝ, 0 ≤ d → (d:EReal) < T →
        (fun z : ℝ => a*Real.sinh (σ*z+θ)) (X (realTimeClamp d) ω) = (fun z : ℝ => a*Real.sinh (σ*z+θ)) (X ⊥ ω)+Z (realTimeClamp d) ω+
          (∫ r in 0..d, (fun z : ℝ => σ^2*(a*Real.sinh (σ*z+θ))) (X (realTimeClamp r) ω))/2 := by
  exact constructed_clock_ito P hT F hF hle hnull X C hX hC
    (fun z => a*Real.sinh (σ*z+θ)) (fun z => σ*(a*Real.cosh (σ*z+θ))) (fun z => σ^2*(a*Real.sinh (σ*z+θ)))
    (by fun_prop) (fun x => (hyperbolic_derivatives a σ θ x).2) (fun x => (hyperbolic_second_derivatives a σ θ x).2) c hc hcm hcT hcc hclock

end Asakura.Chapter4
