import Chapter12PastCylinderApproximation
import Chapter12ClarkTestContinuity
import Chapter12CylinderDirectionDivergence
import Chapter12OrthogonalCylinderTest
import Chapter12LinearCylinder

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The Gaussian increment identity extends to every L4 random variable
measurable with respect to past coordinates. Both the restricted cylinder
approximation and continuity of the two tested expectations are proved. -/
theorem closed_derivative_past_test {Ω H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    [TopologicalSpace K] [FirstCountableTopology K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ)
      (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : K → Ω → ℝ) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ w, Continuous (fun t => X t w))
    (direction : K → H) (hXW : ∀ t, X t =ᵐ[P] (W (direction t) : Ω → ℝ))
    (times : ℕ → K) (htimes : DenseRange times)
    (h : H) (hpast : ∀ t, inner ℝ (direction t) h = 0)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F : D.domain) (G : Lp ℝ 4 P)
    (hgen : AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X t w) inferInstance] G P) :
    (∫ w, G w*inner ℝ (D F w) h ∂P) =
      ∫ w, (F : Lp ℝ 2 P) w*G w*W h w ∂P := by
  let U := (innerSL ℝ h).compLp (D F)
  let B := (linearSmoothCylinder h).valueLp P W S hS hcore 4 (by simp)
  have hU : (U : Ω → ℝ) =ᵐ[P] (fun w => inner ℝ (D F w) h) := by
    filter_upwards [(innerSL ℝ h).coeFn_compLp (D F)] with w hw
    exact hw.trans (real_inner_comm _ _)
  have hB : (B : Ω → ℝ) =ᵐ[P] (W h : Ω → ℝ) := by
    simpa only [B,SmoothCylinder.valueLp,linear_cylinder_value] using
      ((linearSmoothCylinder h).value_memLp P W S hS hcore 4 (by simp)).coeFn_toLp
  let V : Set H := {v | inner ℝ v h = 0}
  have hGc := restricted_cylinder_mem_closure P W S hS hcore X hXm hXc direction hXW
    V hpast times htimes 4 (by simp) G hgen
  have hclosed := clark_test_isClosed P (F : Lp ℝ 2 P) U B
  have hsubset : {J : Lp ℝ 4 P | ∃ c : SmoothCylinder H,
      (∀ j,c.direction j ∈ V) ∧ J = c.valueLp P W S hS hcore 4 (by simp)} ⊆
      {J | (∫ w,J w*U w ∂P) = ∫ w,(F : Lp ℝ 2 P) w*J w*B w ∂P} := by
    rintro J ⟨c,hc,rfl⟩
    have hgrad (w) : inner ℝ (c.gradient P W w) h = 0 :=
      cylinder_derivative_orthogonal c.direction h hc _
    obtain ⟨hi,hd⟩ := cylinder_direction_divergence P W S hS hcore D hgraph c h
    have he := hd F
    rw [L2.inner_def,L2.inner_def] at he
    have hl : (∫ w,inner ℝ (D F w) (hi.toLp _ w) ∂P) =
        ∫ w,c.valueLp P W S hS hcore 4 (by simp) w*U w ∂P := by
      apply integral_congr_ae
      filter_upwards [hi.coeFn_toLp,(c.value_memLp P W S hS hcore 4 (by simp)).coeFn_toLp,hU]
        with w hw hv hu
      rw [hw,inner_smul_right,hu]
      dsimp only [SmoothCylinder.valueLp]
      rw [hv]
    have hr : (∫ w,inner ℝ ((F : Lp ℝ 2 P) w)
        (c.ibpTestLp P W S hS hcore h 2 (by simp) w) ∂P) =
        ∫ w,(F : Lp ℝ 2 P) w*c.valueLp P W S hS hcore 4 (by simp) w*B w ∂P := by
      apply integral_congr_ae
      filter_upwards [(c.ibpTest_memLp P W S hS hcore h 2 (by simp)).coeFn_toLp,
        (c.value_memLp P W S hS hcore 4 (by simp)).coeFn_toLp,hB] with w hw hv hb
      dsimp only [SmoothCylinder.ibpTestLp,SmoothCylinder.valueLp]
      rw [hw,hv,hb]
      change (c.value P W w*W h w-inner ℝ (c.gradient P W w) h)*(F : Lp ℝ 2 P) w = _
      rw [hgrad,sub_zero]
      ring
    exact hl.symm.trans (he.trans hr)
  have he := (closure_minimal hsubset hclosed) hGc
  change (∫ w,G w*U w ∂P) = ∫ w,(F : Lp ℝ 2 P) w*G w*B w ∂P at he
  calc
    _ = ∫ w,G w*U w ∂P := integral_congr_ae (hU.mono (fun w hw => by dsimp only; rw [hw]))
    _ = _ := he
    _ = _ := integral_congr_ae (hB.mono (fun w hw => by dsimp only; rw [hw]))

end Asakura.Chapter12
