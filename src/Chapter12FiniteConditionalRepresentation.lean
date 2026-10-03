import Chapter12BrownianConditionalMartingale

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- A terminal-measurable payoff represented on the half-line already has
its representation at the finite terminal time. This uses conditional expectation,
not an unproved assertion that the future integrands vanish. -/
theorem represented_payoff_at_finite_time {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    {d : ℕ} (N : Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i,ContinuousM2Witness P F (N i))
    (Y : Ω → ℝ) (hY : MemLp Y 2 P) (a : ℝ)
    (he : Y =ᵐ[P] fun w => a+∑ i,N i ⊤ w)
    (τ : HalfClosedTime) (hYm : Measurable[F τ] Y) :
    Y =ᵐ[P] fun w => a+∑ i,N i τ w := by
  let M := fun t w => ∑ i,N i t w
  have hM := finite_sum_continuous_m2 P F hF hle N hN
  have hc := conditional_process_from_represented_terminal P F hle Y hY M hM a he
  have hh := hc.2.2.2 τ
  rw [condExp_of_stronglyMeasurable (hle τ) hYm.stronglyMeasurable
    (hY.integrable (by norm_num))] at hh
  exact hh.symm

end Asakura.Chapter12
