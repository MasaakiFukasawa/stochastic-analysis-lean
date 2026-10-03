import Chapter12StockDerivative

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem constant_derivative_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hgraph : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (a : ℝ) : ((memLp_const (μ := P) (p := p) a).toLp (fun _ => a),0) ∈ D.graph := by
  obtain ⟨hi,hdi,hg⟩ := stock_exponential_derivative_graph P W S hS hcore p hp D hD hgraph a 0
  have hv : hi.toLp _ = (memLp_const (μ := P) (p := p) a).toLp (fun _ => a) := by
    apply Lp.ext
    filter_upwards [hi.coeFn_toLp,(memLp_const (μ := P) (p := p) a).coeFn_toLp,
      Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with w h1 h2 h0
    rw [h1,h2,map_zero,h0]
    simp
  have hu : hdi.toLp _ = 0 := by
    apply Lp.ext
    filter_upwards [hdi.coeFn_toLp,Lp.coeFn_zero (E := H) (p := p) (μ := P)] with w h1 h0
    rw [h1,h0,smul_zero]
    rfl
  rwa [hv,hu] at hg

theorem affine_wiener_derivative_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hgraph : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (h : H) (b : ℝ) :
    ∃ hi : MemLp (fun w => W h w+b) p P,
      (hi.toLp _,(memLp_const (μ := P) (p := p) h).toLp (fun _ => h)) ∈ D.graph := by
  let c := linearSmoothCylinder h
  have hc : (c.valueLp P W S hS hcore p hp,c.gradientLp P W S hS hcore p hp) ∈ D.graph := by
    change cylinderPair P W S hS hcore p hp c ∈ (D.graph : Set _)
    rw [hgraph]
    exact subset_closure (mem_range_self c)
  have hg := D.graph.add_mem hc (constant_derivative_graph P W S hS hcore p hp D hD hgraph b)
  have hi : MemLp (fun w => W h w+b) p P := (c.value_memLp P W S hS hcore p hp).add (memLp_const b)
  refine ⟨hi,?_⟩
  have hv : c.valueLp P W S hS hcore p hp+(memLp_const (μ := P) (p := p) b).toLp (fun _ => b) = hi.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (c.valueLp P W S hS hcore p hp) ((memLp_const (μ := P) (p := p) b).toLp (fun _ => b)),
      (c.value_memLp P W S hS hcore p hp).coeFn_toLp,(memLp_const (μ := P) (p := p) b).coeFn_toLp,
      hi.coeFn_toLp] with w h1 h2 h3 h4
    dsimp only [SmoothCylinder.valueLp] at *
    rw [h1,Pi.add_apply,h2,h3,h4]
    rfl
  have hu : c.gradientLp P W S hS hcore p hp = (memLp_const (μ := P) (p := p) h).toLp (fun _ => h) := by
    apply Lp.ext
    filter_upwards [(c.gradient_memLp P W S hS hcore p hp).coeFn_toLp,
      (memLp_const (μ := P) (p := p) h).coeFn_toLp] with w h1 h2
    dsimp only [SmoothCylinder.gradientLp]
    rw [h1,h2]
    exact congrFun (linear_cylinder_gradient P W h) w
  change (c.valueLp P W S hS hcore p hp+_,c.gradientLp P W S hS hcore p hp+0) ∈ D.graph at hg
  rwa [add_zero,hv,hu] at hg

end Asakura.Chapter12
