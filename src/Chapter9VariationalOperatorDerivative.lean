import Chapter9OperatorJacobian
import Chapter9TimeDependentFlowC1

open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Elementwise
namespace Asakura.Chapter9
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The vector-by-vector variational integral equation really differentiates
as an equation in the complete space of bounded linear operators. -/
theorem variational_integral_operator_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (J A : ℝ → E →L[ℝ] E) (hcJ : Continuous J) (hcA : Continuous A)
    (T : ℝ) (hT : 0≤T)
    (hJ : ∀ t∈Icc 0 T,∀ h,J t h=h+∫ s in 0..t,A s (J s h)) :
    J 0=1 ∧ ∀ t∈Ioo 0 T,HasDerivAt J (A t*J t) t := by
  have he t (ht : t∈Icc 0 T) : J t=1+∫ s in 0..t,A s*J s := by
    ext h
    rw [ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,
      ContinuousLinearMap.intervalIntegral_apply (φ := fun s => A s*J s)
        ((hcA.mul hcJ).intervalIntegrable 0 t)]
    exact hJ t ht h
  refine ⟨by simpa using he 0 ⟨le_rfl,hT⟩,?_⟩
  intro t ht
  have hc := hcA.mul hcJ
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add 1
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  exact he s hs

/-- Positivity of the Jacobian of the initial-state derivative follows from
its actual integral equation and J(0)=Id. -/
theorem variational_operator_determinant_positive {E n : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [Fintype n] [DecidableEq n] (b : Module.Basis n ℝ E)
    (J A : ℝ → E →L[ℝ] E) (hcJ : Continuous J) (hcA : Continuous A)
    (T : ℝ) (hT : 0≤T)
    (hJ : ∀ t∈Icc 0 T,∀ h,J t h=h+∫ s in 0..t,A s (J s h)) :
    0<(J T).det := by
  obtain ⟨h0,hd⟩ := variational_integral_operator_derivative J A hcJ hcA T hT hJ
  have hm0 : operatorMatrix b (J 0)=1 := by
    rw [h0]
    exact LinearMap.toMatrix_one b
  have hm t (ht : t∈Ioo 0 T) : HasDerivAt (fun s => operatorMatrix b (J s))
      (operatorMatrix b (A t)*operatorMatrix b (J t)) t := by
    have hh : HasDerivAt (fun s => operatorMatrix b (J s)) (operatorMatrix b (A t*J t)) t := by
      simpa using (hasDerivAt_const t (operatorMatrix b)).clm_apply (hd t ht)
    simpa only [operator_matrix_mul] using hh
  have hp := variational_determinant_positive (fun s => operatorMatrix b (J s))
    (fun s => operatorMatrix b (A s)) ((operatorMatrix b).continuous.comp hcJ)
    ((operatorMatrix b).continuous.comp hcA) T hT hm0 hm
  simpa only [operator_matrix_det] using hp
end Asakura.Chapter9
