import Chapter9FlowDiffeomorphism
import Chapter9VariationalOperatorDerivative
import Chapter9DensityChangeVariables

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal Matrix.Norms.Elementwise
namespace Asakura.Chapter9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem integral_path_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (b : ℝ → E → E)
    (hb : Continuous b.uncurry) (X : ℝ → E) (hcX : Continuous X)
    (x : E) (T : ℝ)
    (hX : ∀ s∈Icc 0 T,X s=x+∫ r in 0..s,b r (X r)) :
    ∀ s∈Ioo 0 T,HasDerivAt X (b s (X s)) s := by
  have hc := hb.comp (continuous_id.prodMk hcX)
  intro s hs
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add x
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hs.1 hs.2] with t ht
  exact hX t ht

/-- A classical continuity equation is transported by the constructed ODE
flow. The proof constructs the inverse, identifies its actual derivative,
proves its Jacobian identity, and applies change of variables to measures. -/
theorem classical_flow_density_transport {E n : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype n] [DecidableEq n]
    (basis : Module.Basis n ℝ E) (ν : Measure E) [IsAddHaarMeasure ν]
    (b : ℝ → E → E) (D : ℝ → E → E →L[ℝ] E)
    (hb : Continuous b.uncurry) (hcD : Continuous D.uncurry)
    (hD : ∀ t z,HasFDerivAt (b t) (D t z) z)
    (K : ℝ≥0) (hK : ∀ t,LipschitzWith K (b t))
    (T : ℝ) (hT : 0≤T) (p : ℝ × E → ℝ) (hp : Continuous p)
    (DP : ℝ × E → (ℝ × E) →L[ℝ] ℝ)
    (hDP : ∀ t∈Ioo 0 T,∀ x,HasFDerivAt p (DP (t,x)) (t,x))
    (hPDE : ∀ t∈Ioo 0 T,∀ x,DP (t,x) (1,b t x)=
      -p (t,x)*(operatorMatrix basis (D t x)).trace) :
    ∃ e : E ≃ₜ E,Differentiable ℝ e ∧ Differentiable ℝ e.symm ∧
      (ν.withDensity (fun x => ENNReal.ofReal (p (0,x)))).map e=
        ν.withDensity (fun x => ENNReal.ofReal (p (T,x))) ∧
      ∀ x,∃ X : ℝ → E,Continuous X ∧ X T=e x ∧
        ∀ s∈Icc 0 T,X s=x+∫ r in 0..s,b r (X r) := by
  obtain ⟨e,hde,hdinv,hflow⟩ := time_dependent_flow_diffeomorphism b D hb hcD hD K hK T hT
  have hident x : 0<(fderiv ℝ e x).det ∧
      p (T,e x)*(fderiv ℝ e x).det=p (0,x) := by
    obtain ⟨X,hcX,hXT,hX,J,hcJ,hJ,hdJ⟩ := hflow x
    have hcA := hcD.comp (continuous_id.prodMk hcX)
    obtain ⟨hJ0,hJd⟩ := variational_integral_operator_derivative J (fun s => D s (X s)) hcJ hcA T hT hJ
    have hpos := variational_operator_determinant_positive basis J (fun s => D s (X s)) hcJ hcA T hT hJ
    have hdX := integral_path_derivative b hb X hcX x T hX
    have hX0 : X 0=x := by simpa using hX 0 ⟨le_rfl,hT⟩
    let q := fun s => p (s,X s)
    have hcq : Continuous q := hp.comp (continuous_id.prodMk hcX)
    have hdq s (hs : s∈Ioo 0 T) : HasDerivAt q
        (-q s*(operatorMatrix basis (D s (X s))).trace) s := by
      have hh := (hDP s hs (X s)).comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hdX s hs))
      simpa only [hPDE s hs (X s)] using! hh
    have he := interval_constant_of_zero_derivative
      (fun s => q s*(J s).det) T hT
      ((hcq.mul (ContinuousLinearMap.continuous_det.comp hcJ)).continuousOn)
      (fun s hs => transported_density_derivative q (fun r => (J r).det) s
        (operatorMatrix basis (D s (X s))).trace (hdq s hs)
        (operator_determinant_derivative basis J (D s (X s)) s (hJd s hs)))
    rw [hdJ.fderiv]
    refine ⟨hpos,?_⟩
    simpa [q,hXT,hX0,hJ0,ContinuousLinearMap.det] using he
  refine ⟨e,hde,hdinv,?_,?_⟩
  · exact density_transport_change_variables ν e (fderiv ℝ e) (fun x => (hde x).hasFDerivAt)
      (fun x => p (0,x)) (fun x => p (T,x)) (fun x => (hident x).1.le) (fun x => (hident x).2)
  · intro x
    obtain ⟨X,hcX,hXT,hX,_⟩ := hflow x
    exact ⟨X,hcX,hXT,hX⟩
end Asakura.Chapter9
