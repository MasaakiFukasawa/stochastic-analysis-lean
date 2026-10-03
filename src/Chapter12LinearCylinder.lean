import Chapter12ConcreteCylinderOperator

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- All derivatives of a continuous linear map have polynomial growth:
order zero is linear, order one constant, and all higher orders vanish. -/
theorem linear_map_all_derivatives_growth {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k L x‖ ≤ C*(1+‖x‖)^a := by
  cases k with
  | zero =>
    refine ⟨‖L‖,norm_nonneg _,1,fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero,pow_one]
    exact (L.le_opNorm x).trans (mul_le_mul_of_nonneg_left (by linarith : ‖x‖ ≤ 1+‖x‖) (norm_nonneg _))
  | succ k =>
    have hd : fderiv ℝ (fun x => L x) = fun _ => L := funext (fun x => L.fderiv)
    cases k with
    | zero =>
      refine ⟨‖L‖,norm_nonneg _,0,fun x => ?_⟩
      simp only [pow_zero,mul_one]
      change ‖iteratedFDeriv ℝ 1 (fun y => L y) x‖ ≤ ‖L‖
      rw [norm_iteratedFDeriv_one,L.fderiv]
    | succ k =>
      refine ⟨0,le_rfl,0,fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv,hd,iteratedFDeriv_succ_const]
      simp

noncomputable def linearSmoothCylinder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (h : H) : SmoothCylinder H where
  dim := 1
  direction := fun _ => h
  f := fun z => z 0
  df := fun _ => ContinuousLinearMap.proj 0
  smooth := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contDiff
  derivative := fun z => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  growth := polynomial_growth_coordinate 0
  derivative_measurable := fun j => measurable_const
  derivative_growth := fun j => PolyGrowth.const ((ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ) (Pi.single j 1))
  all_derivatives_growth := linear_map_all_derivatives_growth (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ)

theorem linear_cylinder_value {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (h : H) :
    (linearSmoothCylinder h).value P W = (W h : Ω → ℝ) := rfl

theorem linear_cylinder_gradient {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (h : H) :
    (linearSmoothCylinder h).gradient P W = fun _ => h := by
  funext w
  simp [SmoothCylinder.gradient,linearSmoothCylinder,Fin.sum_univ_one]

/-- The concrete cylinder operator has D(W(h))=h, with equality in the
actual L2 graph. This connects the first-chaos examples to its definition. -/
theorem wiener_coordinate_derivative_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hD : ∀ c : SmoothCylinder H,
      (c.valueLp P W S hS hcore 2 (by simp),c.gradientLp P W S hS hcore 2 (by simp)) ∈ D.graph)
    (h : H) : (W h,(memLp_const (μ := P) (p := 2) h).toLp (fun _ => h)) ∈ D.graph := by
  have hd := hD (linearSmoothCylinder h)
  have hv : (linearSmoothCylinder h).valueLp P W S hS hcore 2 (by simp) = W h := by
    apply Lp.ext
    exact ((linearSmoothCylinder h).value_memLp P W S hS hcore 2 (by simp)).coeFn_toLp
  have hg : (linearSmoothCylinder h).gradientLp P W S hS hcore 2 (by simp) =
      (memLp_const (μ := P) (p := 2) h).toLp (fun _ => h) := by
    apply Lp.ext
    filter_upwards [((linearSmoothCylinder h).gradient_memLp P W S hS hcore 2 (by simp)).coeFn_toLp,
      (memLp_const (μ := P) (p := 2) h).coeFn_toLp] with w hw hh
    dsimp only [SmoothCylinder.gradientLp]
    rw [hw,hh]
    exact congrFun (linear_cylinder_gradient P W h) w
  rw [hv,hg] at hd
  exact hd

end Asakura.Chapter12
