import Chapter8LikelihoodCLTAssembly

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- A constant distributional limit is a limit in probability. -/
theorem probability_of_constant_distribution {Ω Γ I E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (l : Filter I) (X : I → Ω → E) (x : E)
    (hX : TendstoInDistribution X l (fun _ : Γ => x) (fun _ => P) Q) :
    TendstoInMeasure P X l (fun _ => x) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  let A : Set E := {y | ε ≤ dist y x}
  have hc : IsClosed A := isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hxa : x ∉ A := by simpa [A] using hε
  have hxf : x ∉ frontier A := fun h => hxa (hc.frontier_subset h)
  have hz : (Q.map (fun _ : Γ => x)) (frontier A) = 0 := by
    simp [Measure.map_const,Measure.dirac_apply' _ isClosed_frontier.measurableSet,hxf]
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hX.tendsto hz
  have hz' : (Q.map (fun _ : Γ => x)) A = 0 := by
    simp [Measure.map_const,Measure.dirac_apply' _ hc.measurableSet,hxa]
  simp only [ProbabilityMeasure.coe_mk, hz'] at ht
  have he (i : I) : P.map (X i) A = P {ω | ε ≤ dist (X i ω) x} := by
    rw [Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable i) hc.measurableSet]
    rfl
  simpa only [he] using ht

/-- A distributionally convergent sequence multiplied by a deterministic
vanishing factor converges to zero in probability. This supplies consistency
from the normalised estimation-error CLT without assuming moment convergence. -/
theorem consistency_from_scaled_clt {Ω Γ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → E) (Z : Γ → E)
    (hX : TendstoInDistribution X atTop Z (fun _ => P) Q)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds 0)) :
    TendstoInMeasure P (fun n ω => a n • X n ω) atTop (fun _ => 0) := by
  have hp : TendstoInMeasure P (fun n (_ : Ω) => a n) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ (fun _ => ha))
  have hd := hX.continuous_comp_prodMk_of_tendstoInMeasure_const
    (show Continuous (fun p : E × ℝ => p.2 • p.1) by fun_prop) hp
    (fun _ => measurable_const.aemeasurable)
  simp only [zero_smul] at hd
  exact probability_of_constant_distribution P Q atTop _ 0 hd

end Asakura.Chapter8
