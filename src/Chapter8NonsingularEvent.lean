import Chapter8MatrixProbability
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace Asakura.Chapter8
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- A formula valid whenever the normalised information matrix is
invertible may fail arbitrarily on the remaining event: its error still
converges to zero in probability. No rate for the bad event is required. -/
theorem probability_error_on_singular_event {Ω I ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    (P : Measure Ω) (l : Filter I) (J : I → Ω → Matrix ι ι ℝ) (S : Matrix ι ι ℝ)
    (hS : S.det ≠ 0) (hJ : TendstoInMeasure P J l (fun _ => S))
    (R : I → Ω → E) (hR : ∀ i ω,(J i ω).det ≠ 0 → R i ω=0) :
    TendstoInMeasure P R l (fun _ => 0) := by
  have hd := probability_continuous_at_constant P l J S hJ Matrix.det
    continuous_id.matrix_det.continuousAt
  have hp := tendstoInMeasure_iff_dist.mp hd |S.det| (abs_pos.mpr hS)
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp (fun _ => bot_le)
  intro i
  apply measure_mono
  intro ω hω
  have hz : (J i ω).det=0 := by
    by_contra hn
    have hr := hR i ω hn
    change ε ≤ ‖R i ω-0‖ at hω
    simp only [sub_zero,hr,norm_zero] at hω
    exact hε.not_ge hω
  simp only [mem_setOf_eq,hz,Real.dist_eq,zero_sub,abs_neg,le_refl]

/-- The preceding error estimate transfers the Gaussian limit to the
estimator as defined on the exceptional singular-information event. -/
theorem distribution_of_nonsingular_formula {Ω Γ ι E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X Y : ℕ → Ω → E) (Z : Γ → E)
    (hX : TendstoInDistribution X atTop Z (fun _ => P) Q) (hmY : ∀ n,AEMeasurable (Y n) P)
    (J : ℕ → Ω → Matrix ι ι ℝ) (S : Matrix ι ι ℝ) (hS : S.det ≠ 0)
    (hJ : TendstoInMeasure P J atTop (fun _ => S))
    (he : ∀ n ω,(J n ω).det ≠ 0 → Y n ω=X n ω) :
    TendstoInDistribution Y atTop Z (fun _ => P) Q := by
  apply tendstoInDistribution_of_tendstoInMeasure_sub Y Z hX _ hmY
  exact probability_error_on_singular_event P atTop J S hS hJ (Y-X)
    (fun n ω h => by simp [Pi.sub_apply,he n ω h])

end Asakura.Chapter8
