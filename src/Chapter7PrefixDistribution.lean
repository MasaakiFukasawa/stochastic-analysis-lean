import Chapter7PathPrefixUniformity
import Chapter7NearbyDistribution

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal Uniformity
namespace Asakura.Chapter7
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Limits of laws on the compact-open continuous path space are unchanged
by alterations after time n. -/
theorem prefix_distribution
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X Y : ℕ → Ω → C(ℝ≥0,ℝ)) (Z : Γ → C(ℝ≥0,ℝ))
    (hX : ∀ n,Measurable (X n)) (hY : ∀ n,Measurable (Y n))
    (hlim : TendstoInDistribution X atTop Z (fun _ => P) Q)
    (he : ∀ (n : ℕ) w t,t ≤ (n:ℝ≥0) → X n w t = Y n w t) :
    TendstoInDistribution Y atTop Z (fun _ => P) Q := by
  letI : MetricSpace C(ℝ≥0,ℝ) := UniformSpace.metricSpace _
  apply nearby_distribution P Q X Y Z hX hY hlim
  apply ae_of_all
  intro w
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => lt_of_lt_of_le ha dist_nonneg)
  · intro ε hε
    have hU : {p : C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ) | dist p.1 p.2 < ε} ∈ 𝓤 C(ℝ≥0,ℝ) :=
      Metric.uniformity_basis_dist.mem_of_mem hε
    obtain ⟨N,hN⟩ := path_prefix_uniformity _ hU
    exact eventually_atTop.2 ⟨N,fun n hn => hN n hn (X n w) (Y n w) (he n w)⟩

end Asakura.Chapter7
