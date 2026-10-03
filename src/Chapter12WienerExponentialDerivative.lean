import Chapter12MalliavinExponential
import Chapter12GaussianExponentialLp
import Chapter12LinearCylinder

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- D exp(W(h)) = exp(W(h)) h in every finite Sobolev Lp graph.
The exponential moments and the approximation in the graph are both proved. -/
theorem wiener_exponential_derivative_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hgraph : (D.graph : Set (Lp ℝ p P × Lp H p P)) =
      closure (range (cylinderPair P W S hS hcore p hp))) (h : H) :
    ∃ hi : MemLp (fun w => Real.exp (W h w)) p P,
    ∃ hdi : MemLp (fun w => Real.exp (W h w) • h) p P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  let c := linearSmoothCylinder h
  let F := c.valueLp P W S hS hcore p hp
  let U := c.gradientLp P W S hS hcore p hp
  have hFU : (F,U) ∈ D.graph := by
    change cylinderPair P W S hS hcore p hp c ∈ (D.graph : Set _)
    rw [hgraph]
    exact subset_closure (mem_range_self c)
  have hv : (F : Ω → ℝ) =ᵐ[P] (W h : Ω → ℝ) :=
    (c.value_memLp P W S hS hcore p hp).coeFn_toLp
  have hu : (U : Ω → H) =ᵐ[P] fun _ => h := by
    dsimp only [U,SmoothCylinder.gradientLp]
    simpa only [linear_cylinder_gradient,c] using (c.gradient_memLp P W S hS hcore p hp).coeFn_toLp
  have hi : MemLp (fun w => Real.exp (W h w)) p P := by
    simpa only [one_mul] using gaussian_exponential_memLp P (W h) 0 ⟨‖h‖^2,sq_nonneg _⟩
      (wiener_gaussian_law_from_dense_core P W S hS hcore h) 1 p hp
  have hdi : MemLp (fun w => Real.exp (W h w) • h) p P :=
    (ContinuousLinearMap.toSpanSingleton ℝ h).comp_memLp' hi
  have he : (fun w => Real.exp (F w)) =ᵐ[P] fun w => Real.exp (W h w) := hv.fun_comp Real.exp
  have heD : (fun w => Real.exp (F w) • U w) =ᵐ[P] fun w => Real.exp (W h w) • h := by
    filter_upwards [he,hu] with w h1 h2
    rw [h1,h2]
  have hi' := hi.ae_eq he.symm
  have hdi' := hdi.ae_eq heD.symm
  have hm := closed_malliavin_exponential_chain P W S hS hcore p hp D hD hgraph F U hFU hi' hdi'
  refine ⟨hi,hdi,?_⟩
  have hv' : hi'.toLp _ = hi.toLp _ := Lp.ext (hi'.coeFn_toLp.trans (he.trans hi.coeFn_toLp.symm))
  have hu' : hdi'.toLp _ = hdi.toLp _ := Lp.ext (hdi'.coeFn_toLp.trans (heD.trans hdi.coeFn_toLp.symm))
  rwa [hv',hu'] at hm

end Asakura.Chapter12
