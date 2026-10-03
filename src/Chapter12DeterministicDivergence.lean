import Chapter12LinearCylinder
import Chapter12DivergenceDuality

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ)
    (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)

include S hS hcore in
theorem SmoothCylinder.direction_ibp (c : SmoothCylinder H) (h : H) :
    (∫ w, ⟪c.gradient P W w,h⟫ ∂P) = ∫ w, c.value P W w*W h w ∂P := by
  have he := wiener_cylindrical_gaussian_ibp P W S hS hcore c.direction
    (fun j : Fin 0 => Fin.elim0 j) h c.f (fun _ => 1) c.df (fun _ => 0)
    c.derivative (fun _ => hasFDerivAt_const 1 _) c.derivative_measurable
    (fun j => Fin.elim0 j) c.growth (PolyGrowth.const 1) c.derivative_growth
    (fun j => Fin.elim0 j)
  simpa only [Finset.univ_eq_empty,Finset.sum_empty,inner_zero_left,one_mul,sub_zero,
    SmoothCylinder.gradient,SmoothCylinder.value] using he

/-- Deterministic divergence is the actual Wiener map used to define the
cylinders; this follows from Gaussian IBP on the generators and linearity. -/
theorem deterministic_divergence_on_cylinder_graph [CompleteSpace H]
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : D.graph = Submodule.span ℝ (range (fun c : SmoothCylinder H =>
      (c.valueLp P W S hS hcore 2 (by simp),c.gradientLp P W S hS hcore 2 (by simp)))))
    (h : H) : IsDivergence D ((memLp_const (μ := P) (p := 2) h).toLp (fun _ => h)) (W h) := by
  let v : Lp H 2 P := (memLp_const h).toLp (fun _ => h)
  let L : (Lp ℝ 2 P × Lp H 2 P) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.snd ℝ _ _)-
    (innerSL ℝ (W h)).comp (ContinuousLinearMap.fst ℝ _ _)
  have hcyl (c : SmoothCylinder H) :
      ⟪v,c.gradientLp P W S hS hcore 2 (by simp)⟫ =
      ⟪W h,c.valueLp P W S hS hcore 2 (by simp)⟫ := by
    rw [L2.inner_def,L2.inner_def]
    have hl : (∫ w, ⟪v w,c.gradientLp P W S hS hcore 2 (by simp) w⟫ ∂P) =
        ∫ w, ⟪c.gradient P W w,h⟫ ∂P := by
      apply integral_congr_ae
      filter_upwards [(memLp_const (μ := P) (p := 2) h).coeFn_toLp,
        (c.gradient_memLp P W S hS hcore 2 (by simp)).coeFn_toLp] with w h1 h2
      dsimp only [v,SmoothCylinder.gradientLp]
      rw [h1,h2,real_inner_comm]
    have hr : (∫ w, inner ℝ (W h w) (c.valueLp P W S hS hcore 2 (by simp) w) ∂P) =
        ∫ w, c.value P W w*W h w ∂P := by
      apply integral_congr_ae
      filter_upwards [(c.value_memLp P W S hS hcore 2 (by simp)).coeFn_toLp] with w hw
      dsimp only [SmoothCylinder.valueLp]
      rw [hw]
      rfl
    rw [hl,hr]
    exact c.direction_ibp P W S hS hcore h
  have hs : D.graph ≤ LinearMap.ker L.toLinearMap := by
    rw [hgraph]
    apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    change ⟪v,c.gradientLp P W S hS hcore 2 (by simp)⟫-
      ⟪W h,c.valueLp P W S hS hcore 2 (by simp)⟫ = 0
    exact sub_eq_zero.mpr (hcyl c)
  intro f
  have he := hs (D.mem_graph f)
  change ⟪v,D f⟫-⟪W h,(f : Lp ℝ 2 P)⟫ = 0 at he
  calc
    _ = ⟪v,D f⟫ := real_inner_comm _ _
    _ = ⟪W h,(f : Lp ℝ 2 P)⟫ := sub_eq_zero.mp he
    _ = _ := real_inner_comm _ _

end Asakura.Chapter12
