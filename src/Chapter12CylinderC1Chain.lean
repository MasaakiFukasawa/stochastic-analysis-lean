import Chapter12CylinderSmoothChain
import Chapter12C1ClosedGraph

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The C1 chain rule on the defining cylinder class, with membership of
all smooth approximants derived from the actual cylinder construction. -/
theorem cylinder_C1_chain {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hDc : ∀ c : SmoothCylinder H,
      (c.valueLp P W S hS hcore p hp,c.gradientLp P W S hS hcore p hp) ∈ D.graph)
    (c : SmoothCylinder H) (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (hdc : Continuous df)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |df x| ≤ C) :
    ∃ (hi : MemLp (fun w => f (c.value P W w)) p P)
      (hdi : MemLp (fun w => df (c.value P W w) • c.gradient P W w) p P),
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  apply bounded_C1_chain_by_closed_graph P p hp D hD (c.value P W)
    (c.smooth.continuous.measurable.comp (Measurable.of_eval (fun j =>
      (Lp.stronglyMeasurable (W (c.direction j))).measurable)))
    (c.value_memLp P W S hS hcore p hp) (c.gradient P W)
    (c.gradient_memLp P W S hS hcore p hp) f df hd hdc C hC hb
  intro g dg hg hdg hgb hi hdi
  let e := composeSmoothCylinder c g hg hgb
  have he := hDc e
  have hval : e.valueLp P W S hS hcore p hp = hi.toLp _ := by
    apply Lp.ext
    filter_upwards [(e.value_memLp P W S hS hcore p hp).coeFn_toLp,hi.coeFn_toLp] with w h1 h2
    dsimp only [SmoothCylinder.valueLp]
    rw [h1,h2]
    rfl
  have hder : e.gradientLp P W S hS hcore p hp = hdi.toLp _ := by
    apply Lp.ext
    filter_upwards [(e.gradient_memLp P W S hS hcore p hp).coeFn_toLp,hdi.coeFn_toLp] with w h1 h2
    dsimp only [SmoothCylinder.gradientLp]
    rw [h1,h2]
    exact congrFun (composeSmoothCylinder_gradient P W c g dg hg hdg hgb) w
  rw [hval,hder] at he
  exact he

end Asakura.Chapter12
