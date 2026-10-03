import Chapter8ProbabilityContinuous
import Chapter8GaussianProjection
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology MatrixOrder Matrix.Norms.Elementwise
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

theorem probability_continuous_within_at_constant {Ω I E G : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [PseudoMetricSpace G]
    (P : Measure Ω) (l : Filter I) (X : I → Ω → E) (x : E)
    (hX : TendstoInMeasure P X l (fun _ => x)) (s : Set E)
    (hs : ∀ i ω,X i ω ∈ s) (f : E → G) (hf : ContinuousWithinAt f s x) :
    TendstoInMeasure P (fun i ω => f (X i ω)) l (fun _ => f x) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousWithinAt_iff.mp hf ε hε
  have hh := tendstoInMeasure_iff_dist.mp hX δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro i
  apply measure_mono
  intro ω hω
  by_contra hn
  exact (not_le_of_gt (hd (hs i ω) (lt_of_not_ge hn))) hω

open scoped Matrix.Norms.L2Operator in
theorem matrix_sqrt_continuous_on {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousOn (CFC.sqrt : Matrix ι ι ℝ → Matrix ι ι ℝ) {A | A.PosSemidef} := by
  exact CFC.continuousOn_sqrt.mono (fun _ h => h.nonneg)

open scoped Matrix.Norms.L2Operator in
theorem matrix_sqrt_measurable {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (CFC.sqrt : Matrix ι ι ℝ → Matrix ι ι ℝ) := CFC.measurable_sqrt

/-- The observed information is positive semidefinite; square-root
continuity is needed only on that cone, not on all matrices. -/
theorem probability_information_square_root {Ω I ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (l : Filter I) (J : I → Ω → Matrix ι ι ℝ) (S : Matrix ι ι ℝ)
    (hS : S.PosSemidef) (hJpos : ∀ i ω,(J i ω).PosSemidef)
    (hJ : TendstoInMeasure P J l (fun _ => S)) :
    TendstoInMeasure P (fun i ω => CFC.sqrt (J i ω)) l (fun _ => CFC.sqrt S) := by
  exact probability_continuous_within_at_constant P l J S hJ _ hJpos CFC.sqrt
    (matrix_sqrt_continuous_on S hS)

end Asakura.Chapter8
