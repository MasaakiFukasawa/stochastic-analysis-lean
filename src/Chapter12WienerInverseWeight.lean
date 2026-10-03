import Chapter12DivergenceClosureCompatibility

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The first-chaos density weight is obtained from the same closed D and
its divergence, rather than a separately postulated Wiener integral. -/
theorem wiener_inverse_covariance_weight
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    [CompleteSpace H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore 2 (by simp)))
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (h : H) (hh : h ≠ 0) :
    (W h,(memLp_const (μ := P) (p := 2) h).toLp (fun _ => h)) ∈ D.graph ∧
    inner ℝ h ((‖h‖^2)⁻¹ • h) = 1 ∧
    IsDivergence D ((memLp_const (μ := P) (p := 2) ((‖h‖^2)⁻¹ • h)).toLp
      (fun _ => (‖h‖^2)⁻¹ • h)) ((‖h‖^2)⁻¹ • W h) := by
  refine ⟨?_,?_,?_⟩
  · apply wiener_coordinate_derivative_graph P W S hS hcore D _ h
    intro c
    change cylinderPair P W S hS hcore 2 (by simp) c ∈ (D.graph : Set _)
    rw [hgraph]
    exact subset_closure (mem_range_self c)
  · rw [inner_smul_right,real_inner_self_eq_norm_sq]
    exact inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hh))
  · simpa only [map_smul] using
      deterministic_divergence_on_closed_graph P W S hS hcore hdense D hgraph ((‖h‖^2)⁻¹ • h)

end Asakura.Chapter12
