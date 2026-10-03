import Chapter12CylinderC1Chain
import Chapter12C1SequenceGraph
import Chapter12CylinderPairLinear

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The C1 chain rule for the closed Malliavin derivative. Both approximation
steps are constructed: smoothing the outer function and approximating a
graph point by the manuscript's smooth cylinders. -/
theorem closed_malliavin_C1_chain {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hgraph : (D.graph : Set (Lp ℝ p P × Lp H p P)) =
      closure (range (cylinderPair P W S hS hcore p hp)))
    (F₀ : Lp ℝ p P) (U₀ : Lp H p P) (hFU : (F₀,U₀) ∈ D.graph)
    (f df : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (df x) x) (hdc : Continuous df)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |df x| ≤ C) :
    ∃ hi : MemLp (fun w => df (F₀ w) • U₀ w) p P,
      (lipschitzCompositionLp P p (bounded_derivative_lipschitz f df hd C hC hb) F₀,hi.toLp _) ∈ D.graph := by
  have hcl : (F₀,U₀) ∈ closure (range (cylinderPair P W S hS hcore p hp)) := by
    rw [← hgraph]
    exact hFU
  obtain ⟨z,hz,hzt⟩ := mem_closure_iff_seq_limit.mp hcl
  choose c hc using hz
  have hzEq : z = fun n => cylinderPair P W S hS hcore p hp (c n) :=
    funext fun n => (hc n).symm
  rw [hzEq] at hzt
  let F := fun n => (c n).valueLp P W S hS hcore p hp
  let U := fun n => (c n).gradientLp P W S hS hcore p hp
  have hF : Tendsto F atTop (𝓝 F₀) := by
    exact (continuous_fst.tendsto (F₀,U₀)).comp hzt
  have hU : Tendsto U atTop (𝓝 U₀) := by
    exact (continuous_snd.tendsto (F₀,U₀)).comp hzt
  have hDc (e : SmoothCylinder H) :
      (e.valueLp P W S hS hcore p hp,e.gradientLp P W S hS hcore p hp) ∈ D.graph := by
    change cylinderPair P W S hS hcore p hp e ∈ (D.graph : Set _)
    rw [hgraph]
    exact subset_closure (mem_range_self _)
  apply C1_chain_limit_in_closed_graph P p hp D hD F U F₀ U₀ hF hU f df hd hdc C hC hb
  intro n
  obtain ⟨hi,hdi,hmem⟩ := cylinder_C1_chain P W S hS hcore p hp D hD hDc (c n) f df hd hdc C hC hb
  have hv : (F n : Ω → ℝ) =ᵐ[P] (c n).value P W := (c n).value_memLp P W S hS hcore p hp |>.coeFn_toLp
  have hu : (U n : Ω → H) =ᵐ[P] (c n).gradient P W := (c n).gradient_memLp P W S hS hcore p hp |>.coeFn_toLp
  have he : (fun w => df (F n w) • U n w) =ᵐ[P]
      fun w => df ((c n).value P W w) • (c n).gradient P W w := by
    filter_upwards [hv,hu] with w h1 h2
    rw [h1,h2]
  have hdi' : MemLp (fun w => df (F n w) • U n w) p P := hdi.ae_eq he.symm
  refine ⟨hdi',?_⟩
  have heV : lipschitzCompositionLp P p (bounded_derivative_lipschitz f df hd C hC hb) (F n) = hi.toLp _ := by
    apply Lp.ext
    exact (lipschitzCompositionLp_coe P p _ (F n)).trans
      ((hv.fun_comp f).trans hi.coeFn_toLp.symm)
  have heU : hdi'.toLp _ = hdi.toLp _ := by
    apply Lp.ext
    exact hdi'.coeFn_toLp.trans (he.trans hdi.coeFn_toLp.symm)
  rw [heV,heU]
  exact hmem

end Asakura.Chapter12
