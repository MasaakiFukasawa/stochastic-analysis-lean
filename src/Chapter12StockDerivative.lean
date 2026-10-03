import Chapter12WienerExponentialDerivative

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The Black--Scholes stock derivative, with every moment and membership
in the closed derivative graph justified. The deterministic factor A
contains the initial stock price and the time drift. -/
theorem stock_exponential_derivative_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hgraph : (D.graph : Set (Lp ℝ p P × Lp H p P)) =
      closure (range (cylinderPair P W S hS hcore p hp))) (A : ℝ) (h : H) :
    ∃ hi : MemLp (fun w => A*Real.exp (W h w)) p P,
    ∃ hdi : MemLp (fun w => (A*Real.exp (W h w)) • h) p P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  obtain ⟨hi,hdi,hd⟩ := wiener_exponential_derivative_graph P W S hS hcore p hp D hD hgraph h
  have hi' := hi.const_mul A
  have hdi' : MemLp (fun w => (A*Real.exp (W h w)) • h) p P :=
    (ContinuousLinearMap.toSpanSingleton ℝ h).comp_memLp' hi'
  refine ⟨hi',hdi',?_⟩
  have hm := D.graph.smul_mem A hd
  have hv : A • hi.toLp _ = hi'.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul A (hi.toLp _),hi.coeFn_toLp,hi'.coeFn_toLp] with w h1 h2 h3
    rw [h1,Pi.smul_apply,h2,h3]
    rfl
  have hu : A • hdi.toLp _ = hdi'.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul A (hdi.toLp _),hdi.coeFn_toLp,hdi'.coeFn_toLp] with w h1 h2 h3
    rw [h1,Pi.smul_apply,h2,h3,smul_smul]
  change (A • hi.toLp _,A • hdi.toLp _) ∈ D.graph at hm
  rwa [hv,hu] at hm

end Asakura.Chapter12
