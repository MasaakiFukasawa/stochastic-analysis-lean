import Chapter12CylinderDirectionDivergence
import Chapter12DivergenceRawPairing

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Duality on the actual smooth core extends to the closed derivative
graph because the two L2 pairings are continuous. -/
theorem divergence_of_raw_cylinder_tests {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (U : Ω → H) (Z : Ω → ℝ) (hU : MemLp U 2 P) (hZ : MemLp Z 2 P)
    (htest : ∀ c : SmoothCylinder H,
      (∫ w,inner ℝ (c.gradient P W w) (U w) ∂P)=∫ w,c.value P W w*Z w ∂P) :
    IsDivergence D (hU.toLp _) (hZ.toLp _) := by
  have hc (c : SmoothCylinder H) :
      inner ℝ (c.gradientLp P W S hS hcore 2 (by simp)) (hU.toLp _)=
      inner ℝ (c.valueLp P W S hS hcore 2 (by simp)) (hZ.toLp _) := by
    rw [L2.inner_def,L2.inner_def]
    calc
      _=(∫ w,inner ℝ (c.gradient P W w) (U w) ∂P) := by
        apply integral_congr_ae
        filter_upwards [(c.gradient_memLp P W S hS hcore 2 (by simp)).coeFn_toLp,hU.coeFn_toLp] with w hc hu
        change inner ℝ ((c.gradient_memLp P W S hS hcore 2 (by simp)).toLp _ w) (hU.toLp _ w)=_
        rw [hc,hu]
      _=(∫ w,c.value P W w*Z w ∂P) := htest c
      _=_ := by
        apply integral_congr_ae
        filter_upwards [(c.value_memLp P W S hS hcore 2 (by simp)).coeFn_toLp,hZ.coeFn_toLp] with w hc hz
        change _=inner ℝ ((c.value_memLp P W S hS hcore 2 (by simp)).toLp _ w) (hZ.toLp _ w)
        rw [hc,hz]
        simp [RCLike.inner_apply,mul_comm]
  have hsub : closure (range (cylinderPair P W S hS hcore 2 (by simp))) ⊆
      {a : Lp ℝ 2 P × Lp H 2 P | inner ℝ a.2 (hU.toLp _)=inner ℝ a.1 (hZ.toLp _)} := by
    apply closure_minimal
    · rintro _ ⟨c,rfl⟩
      exact hc c
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  intro f
  have hf := D.mem_graph f
  change ((f : Lp ℝ 2 P),D f)∈(D.graph : Set (Lp ℝ 2 P × Lp H 2 P)) at hf
  rw [hgraph] at hf
  exact hsub hf

end Asakura.Chapter12
