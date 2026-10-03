import FullAuditChapter4Obstructions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Filter
open scoped Topology
namespace Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

/-- The geometric Brownian example's first and second spatial derivatives. -/
theorem exponential_derivatives (y x : ℝ) :
    HasDerivAt (fun z => y*Real.exp z) (y*Real.exp x) x ∧
    HasDerivAt (deriv (fun z => y*Real.exp z)) (y*Real.exp x) x := by
  have h z := (Real.hasDerivAt_exp z).const_mul y
  refine ⟨h x,?_⟩
  have he : deriv (fun z => y*Real.exp z) = fun z => y*Real.exp z :=
    funext (fun z => (h z).deriv)
  rw [he]
  exact h x

theorem circle_derivatives (a σ θ x : ℝ) :
    HasDerivAt (fun z => a*Real.cos (σ*z+θ)) (-σ*(a*Real.sin (σ*x+θ))) x ∧
    HasDerivAt (fun z => a*Real.sin (σ*z+θ)) (σ*(a*Real.cos (σ*x+θ))) x := by
  constructor
  · convert (((hasDerivAt_id x).const_mul σ).add_const θ).cos.const_mul a using 1 <;> dsimp <;> ring
  · convert (((hasDerivAt_id x).const_mul σ).add_const θ).sin.const_mul a using 1 <;> dsimp <;> ring

theorem circle_second_derivatives (a σ θ x : ℝ) :
    HasDerivAt (fun z => -σ*(a*Real.sin (σ*z+θ))) (-σ^2*(a*Real.cos (σ*x+θ))) x ∧
    HasDerivAt (fun z => σ*(a*Real.cos (σ*z+θ))) (-σ^2*(a*Real.sin (σ*x+θ))) x := by
  constructor
  · convert ((circle_derivatives a σ θ x).2).const_mul (-σ) using 1 <;> ring
  · convert ((circle_derivatives a σ θ x).1).const_mul σ using 1 <;> ring

theorem circle_constraint (a x : ℝ) :
    (a*Real.cos x)^2+(a*Real.sin x)^2=a^2 := by
  nlinarith [Real.sin_sq_add_cos_sq x,
    congrArg (fun z : ℝ => a^2*z) (Real.sin_sq_add_cos_sq x)]

theorem hyperbolic_derivatives (a σ θ x : ℝ) :
    HasDerivAt (fun z => a*Real.cosh (σ*z+θ)) (σ*(a*Real.sinh (σ*x+θ))) x ∧
    HasDerivAt (fun z => a*Real.sinh (σ*z+θ)) (σ*(a*Real.cosh (σ*x+θ))) x := by
  constructor
  · convert (((hasDerivAt_id x).const_mul σ).add_const θ).cosh.const_mul a using 1 <;> dsimp <;> ring
  · convert (((hasDerivAt_id x).const_mul σ).add_const θ).sinh.const_mul a using 1 <;> dsimp <;> ring

theorem hyperbolic_second_derivatives (a σ θ x : ℝ) :
    HasDerivAt (fun z => σ*(a*Real.sinh (σ*z+θ))) (σ^2*(a*Real.cosh (σ*x+θ))) x ∧
    HasDerivAt (fun z => σ*(a*Real.cosh (σ*z+θ))) (σ^2*(a*Real.sinh (σ*x+θ))) x := by
  constructor
  · convert ((hyperbolic_derivatives a σ θ x).2).const_mul σ using 1 <;> ring
  · convert ((hyperbolic_derivatives a σ θ x).1).const_mul σ using 1 <;> ring

theorem hyperbolic_constraint (a x : ℝ) :
    (a*Real.cosh x)^2-(a*Real.sinh x)^2=a^2 := by
  nlinarith [Asakura.FullAudit.ch4_hyperbolic_scaled_square a x]

/-- The second derivative of the ODE solution is the Ito correction appearing
in the Stratonovich example. -/
theorem ode_second_derivative (φ f f' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (f (φ x)) x)
    (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (deriv φ) (f' (φ x)*f (φ x)) x := by
  have he : deriv φ = fun z => f (φ z) := funext (fun z => (hφ z).deriv)
  rw [he]
  exact (hf (φ x)).comp x (hφ x)

/-- The exercise needs only pointwise convergence: continuity of φ transports
it to the candidate solution, with no uniform convergence assumption. -/
theorem ode_composition_limit (φ : ℝ → ℝ) (hφ : Continuous φ)
    (w : ℕ → ℝ) (b : ℝ) (hw : Tendsto w atTop (𝓝 b)) :
    Tendsto (fun n => φ (w n)) atTop (𝓝 (φ b)) :=
  hφ.continuousAt.tendsto.comp hw


/-- The sign and scale in the scalar hyperbolic SDE, including negative a. -/
theorem hyperbolic_scalar_diffusion (a x : ℝ) :
    SignType.sign a * Real.sqrt (a^2+|a*Real.sinh x|^2) = a*Real.cosh x := by
  have hsq : a^2+|a*Real.sinh x|^2 = (a*Real.cosh x)^2 := by
    rw [sq_abs]
    nlinarith [hyperbolic_constraint a x]
  rw [hsq,Real.sqrt_sq_eq_abs,abs_mul,abs_of_pos (Real.cosh_pos x),
    ← mul_assoc,sign_mul_abs]


/-- Smoothness of the ODE solution needed for Ito follows from the ODE;
no extra C2 assumption on the solution is necessary. -/
theorem ode_solution_c2 (φ f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hφ : ∀ x, HasDerivAt φ (f (φ x)) x) : ContDiff ℝ 2 φ := by
  have hd : Differentiable ℝ φ := fun x => (hφ x).differentiableAt
  have he : deriv φ = fun x => f (φ x) := funext (fun x => (hφ x).deriv)
  have h1 : ContDiff ℝ 1 φ := contDiff_one_iff_deriv.mpr
    ⟨hd,by rw [he]; exact hf.continuous.comp hd.continuous⟩
  rw [show (2:WithTop ℕ∞) = 1+1 by rfl,contDiff_succ_iff_deriv]
  refine ⟨hd,by norm_num,?_⟩
  rw [he]
  exact hf.comp h1

end Asakura.Chapter4
