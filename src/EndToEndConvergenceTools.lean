import EndToEndProbabilityTests
import EndToEndJointConvergence

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Asakura.EndToEnd
set_option backward.isDefEq.respectTransparency false

/-- The direct bounded-test proof of probability implying distribution. -/
theorem probability_distribution_written
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (Y : Ω → E)
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hp : TendstoInMeasure P X atTop Y) :
    TendstoInDistribution X atTop Y (fun _ => P) P := by
  letI : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  let e := Y (Classical.choice inferInstance)
  refine ⟨fun n => (hX n).aemeasurable,hY.aemeasurable,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hφb hφl
  obtain ⟨C,hC⟩ := hφb
  obtain ⟨L,hL⟩ := hφl
  have hb x : |φ x| ≤ |φ e|+C := by
    have hh := norm_sub_le (φ x-φ e) (-φ e)
    have hbound := hC x e
    rw [Real.dist_eq] at hbound
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg,Real.norm_eq_abs] at hh
    linarith
  have hlim := probability_test_limit P X Y hX hY hp φ hL.uniformContinuous _ hb
  have hl := hlim.add (tendsto_const_nhds (x := ∫ w,φ (Y w) ∂P))
  simp only [sub_add_cancel,zero_add] at hl
  change Tendsto (fun n => ∫ x,φ x ∂P.map (X n)) atTop (𝓝 (∫ x,φ x ∂P.map Y))
  simpa only [integral_map (hX _).aemeasurable hL.continuous.measurable.aestronglyMeasurable,
    integral_map hY.aemeasurable hL.continuous.measurable.aestronglyMeasurable] using hl

/-- Continuous functions of the joint limit, with no independence assumption. -/
theorem joint_continuous_convergence
    {Ω E H G : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MetricSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (A : ℕ → Ω → H) (Y : Ω → E) (a : H)
    (hX : ∀ n,Measurable (X n)) (hA : ∀ n,Measurable (A n)) (hY : Measurable Y)
    (hlim : TendstoInDistribution X atTop Y (fun _ => P) P)
    (hp : TendstoInMeasure P A atTop (fun _ => a))
    (g : E × H → G) (hg : Continuous g) :
    TendstoInDistribution (fun n w => g (X n w,A n w)) atTop
      (fun w => g (Y w,a)) (fun _ => P) P := by
  letI : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  letI : Nonempty E := ⟨Y (Classical.choice inferInstance)⟩
  exact (joint_probability_distribution P X A Y a hX hA hY hlim hp).continuous_comp hg

#print axioms probability_distribution_written
#print axioms joint_continuous_convergence
end Asakura.EndToEnd
