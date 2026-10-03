import Chapter12DeterministicDivergence
import Chapter12CylinderPairLinear

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The finite-sum divergence formula for one term G h, on the actual
closed Malliavin graph. Linearity then handles every finite sum. -/
theorem cylinder_direction_divergence {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D.graph : Set (Lp ℝ 2 P × Lp H 2 P)) =
      closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (G : SmoothCylinder H) (h : H) :
    ∃ hi : MemLp (fun w => G.value P W w • h) 2 P,
      IsDivergence D (hi.toLp _) (G.ibpTestLp P W S hS hcore h 2 (by simp)) := by
  have hi : MemLp (fun w => G.value P W w • h) 2 P :=
    (ContinuousLinearMap.toSpanSingleton ℝ h).comp_memLp' (G.value_memLp P W S hS hcore 2 (by simp))
  let v := hi.toLp _
  let z := G.ibpTestLp P W S hS hcore h 2 (by simp)
  have hc (c : SmoothCylinder H) :
      ⟪c.gradientLp P W S hS hcore 2 (by simp),v⟫ =
      ⟪c.valueLp P W S hS hcore 2 (by simp),z⟫ := by
    rw [L2.inner_def,L2.inner_def]
    have hl : (∫ w, ⟪c.gradientLp P W S hS hcore 2 (by simp) w,v w⟫ ∂P) =
        ∫ w, ⟪h,c.gradientLp P W S hS hcore 2 (by simp) w⟫*
          G.valueLp P W S hS hcore 2 (by simp) w ∂P := by
      apply integral_congr_ae
      filter_upwards [hi.coeFn_toLp,(G.value_memLp P W S hS hcore 2 (by simp)).coeFn_toLp] with w hv hg
      change ⟪_,hi.toLp _ w⟫ = _
      dsimp only [SmoothCylinder.valueLp]
      rw [hv,hg,inner_smul_right,real_inner_comm h]
      ring
    rw [hl]
    rw [c.Lp_ibp P W S hS hcore G h 2 2 (by simp) (by simp)]
    apply integral_congr_ae
    exact ae_of_all P fun w => mul_comm _ _
  have hs : closure (range (cylinderPair P W S hS hcore 2 (by simp))) ⊆
      {a : Lp ℝ 2 P × Lp H 2 P | ⟪a.2,v⟫ = ⟪a.1,z⟫} := by
    apply closure_minimal
    · rintro _ ⟨c,rfl⟩
      exact hc c
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  refine ⟨hi,fun f => ?_⟩
  have hf := D.mem_graph f
  change ((f : Lp ℝ 2 P),D f) ∈ (D.graph : Set _) at hf
  rw [hgraph] at hf
  exact hs hf

end Asakura.Chapter12
