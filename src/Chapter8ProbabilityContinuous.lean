import Chapter8ProbabilityLinear
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.MeasurableSpace

open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Elementwise
namespace Asakura.Chapter8

/-- Continuity only at the deterministic limiting value suffices. This is
why a matrix inverse need not be continuous at singular matrices. -/
theorem probability_continuous_at_constant {Ω I E G : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [PseudoMetricSpace G]
    (P : Measure Ω) (l : Filter I) (X : I → Ω → E) (x : E)
    (hX : TendstoInMeasure P X l (fun _ => x)) (f : E → G) (hf : ContinuousAt f x) :
    TendstoInMeasure P (fun i ω => f (X i ω)) l (fun _ => f x) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hf ε hε
  have hh := tendstoInMeasure_iff_dist.mp hX δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro i
  apply measure_mono
  intro ω hω
  by_contra hn
  have ht := hd (show dist (X i ω) x < δ from lt_of_not_ge hn)
  exact (not_le_of_gt ht) hω

/-- Matrix inversion in probability at an invertible deterministic matrix. -/
theorem probability_matrix_inverse {Ω I ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (l : Filter I) (J : I → Ω → Matrix ι ι ℝ) (S : Matrix ι ι ℝ)
    (hS : S.det ≠ 0) (hJ : TendstoInMeasure P J l (fun _ => S)) :
    TendstoInMeasure P (fun i ω => (J i ω)⁻¹) l (fun _ => S⁻¹) := by
  apply probability_continuous_at_constant P l J S hJ Inv.inv
  apply continuousAt_matrix_inv S
  simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hS)

end Asakura.Chapter8
