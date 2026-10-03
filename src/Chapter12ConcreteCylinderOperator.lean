import Chapter12CylinderGraph
import Chapter12IBPTestMoments

open MeasureTheory ProbabilityTheory Set Filter ENNReal
open scoped Topology RealInnerProductSpace ContDiff
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- A smooth cylinder with polynomial growth of every derivative, as in
the manuscript. The first derivative is also recorded explicitly. -/
structure SmoothCylinder (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  dim : ℕ
  direction : Fin dim → H
  f : (Fin dim → ℝ) → ℝ
  df : (Fin dim → ℝ) → (Fin dim → ℝ) →L[ℝ] ℝ
  smooth : ContDiff ℝ ∞ f
  derivative : ∀ x, HasFDerivAt f (df x) x
  growth : PolyGrowth f
  derivative_measurable : ∀ j, Measurable (fun x => df x (Pi.single j 1))
  derivative_growth : ∀ j, PolyGrowth (fun x => df x (Pi.single j 1))
  all_derivatives_growth : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℕ,
    ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C*(1+‖x‖)^a

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ)
    (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)

noncomputable def SmoothCylinder.value (c : SmoothCylinder H) : Ω → ℝ :=
  fun w => c.f (fun j => W (c.direction j) w)
noncomputable def SmoothCylinder.gradient (c : SmoothCylinder H) : Ω → H :=
  fun w => ∑ j, c.df (fun i => W (c.direction i) w) (Pi.single j 1) • c.direction j

include S hS hcore

theorem SmoothCylinder.value_memLp (c : SmoothCylinder H) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (c.value P W) p P :=
  wiener_cylinder_memLp P W S hS hcore c.direction c.f c.smooth.continuous.measurable c.growth p hp

theorem SmoothCylinder.gradient_memLp (c : SmoothCylinder H) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (c.gradient P W) p P :=
  wiener_cylinder_derivative_memLp P W S hS hcore c.direction
    (fun j x => c.df x (Pi.single j 1)) c.derivative_measurable c.derivative_growth p hp

noncomputable def SmoothCylinder.valueLp (c : SmoothCylinder H) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    Lp ℝ p P := (c.value_memLp P W S hS hcore p hp).toLp _
noncomputable def SmoothCylinder.gradientLp (c : SmoothCylinder H) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    Lp H p P := (c.gradient_memLp P W S hS hcore p hp).toLp _

noncomputable def SmoothCylinder.ibpTest (c : SmoothCylinder H) (h : H) : Ω → ℝ :=
  fun w => c.value P W w*W h w-⟪c.gradient P W w,h⟫

theorem SmoothCylinder.ibpTest_memLp (c : SmoothCylinder H) (h : H)
    (q : ℝ≥0∞) (hq : q ≠ ⊤) : MemLp (c.ibpTest P W h) q P :=
  gaussian_ibp_test_memLp P W S hS hcore c.direction c.f
    (fun j x => c.df x (Pi.single j 1)) c.smooth.continuous.measurable c.growth
    c.derivative_measurable c.derivative_growth h q hq

noncomputable def SmoothCylinder.ibpTestLp (c : SmoothCylinder H) (h : H)
    (q : ℝ≥0∞) (hq : q ≠ ⊤) : Lp ℝ q P :=
  (c.ibpTest_memLp P W S hS hcore h q hq).toLp _

theorem SmoothCylinder.Lp_ibp (c d : SmoothCylinder H) (h : H)
    (p q : ℝ≥0∞) (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    (∫ w, ⟪h,c.gradientLp P W S hS hcore p hp w⟫*
      d.valueLp P W S hS hcore q hq w ∂P) =
    ∫ w, c.valueLp P W S hS hcore p hp w*
      d.ibpTestLp P W S hS hcore h q hq w ∂P := by
  have hl : (fun w => ⟪h,c.gradientLp P W S hS hcore p hp w⟫*
      d.valueLp P W S hS hcore q hq w) =ᵐ[P]
      fun w => d.value P W w*⟪c.gradient P W w,h⟫ := by
    filter_upwards [(c.gradient_memLp P W S hS hcore p hp).coeFn_toLp,
      (d.value_memLp P W S hS hcore q hq).coeFn_toLp] with w hw hd
    dsimp only [gradientLp,valueLp]
    rw [hw,hd,real_inner_comm,mul_comm]
  have hr : (fun w => c.valueLp P W S hS hcore p hp w*
      d.ibpTestLp P W S hS hcore h q hq w) =ᵐ[P]
      fun w => c.value P W w*d.ibpTest P W h w := by
    filter_upwards [(c.value_memLp P W S hS hcore p hp).coeFn_toLp,
      (d.ibpTest_memLp P W S hS hcore h q hq).coeFn_toLp] with w hw hd
    dsimp only [valueLp,ibpTestLp]
    rw [hw,hd]
  rw [integral_congr_ae hl,integral_congr_ae hr]
  exact wiener_cylindrical_gaussian_ibp P W S hS hcore c.direction d.direction h
    c.f d.f c.df d.df c.derivative d.derivative c.derivative_measurable
    d.derivative_measurable c.growth d.growth c.derivative_growth d.derivative_growth

/-- The concrete values, derivatives, and Gaussian IBP tests are inserted
into the Lp graph construction. Only density of the cylinder values remains
as an input; no derivative operator or IBP identity is assumed. -/
theorem concrete_cylinder_operator [SecondCountableTopology H]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq)) :
    ∃ D : Lp ℝ p P →ₗ.[ℝ] Lp H p P,
      D.graph = Submodule.span ℝ (range (fun c : SmoothCylinder H =>
        (c.valueLp P W S hS hcore p hp,c.gradientLp P W S hS hcore p hp))) ∧
      D.IsClosable ∧ ∀ c : SmoothCylinder H,
        (c.valueLp P W S hS hcore p hp,c.gradientLp P W S hS hcore p hp) ∈ D.graph := by
  classical
  let tests := range (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq)
  let select (v : tests) : SmoothCylinder H := v.property.choose
  have hselect (v : tests) : (select v).valueLp P W S hS hcore q hq = v.val :=
    v.property.choose_spec
  apply Lp_operator_from_cylinder_pairs P p q _ _ tests hdense
    (fun v h => (select v).ibpTestLp P W S hS hcore h q hq)
  intro c v h
  rw [← hselect v]
  exact c.Lp_ibp P W S hS hcore (select v) h p q hp hq

end Asakura.Chapter12
