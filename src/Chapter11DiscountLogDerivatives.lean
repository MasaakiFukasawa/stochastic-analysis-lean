import Chapter11AffineBarrierCandidate

open Set Filter
open scoped Topology
namespace Asakura.Chapter11
set_option maxHeartbeats 3800000

/-- The space derivatives in the logarithmic and discounted coordinates.
 Only two space derivatives of the original function are used. -/
theorem discount_log_space_derivatives (f : ℝ → ℝ) (b d y : ℝ)
    (hf : ContDiffAt ℝ 2 f (b*Real.exp y)) :
    deriv (fun z => d*f (b*Real.exp z)) y=d*(b*Real.exp y)*deriv f (b*Real.exp y) ∧
    deriv (deriv (fun z => d*f (b*Real.exp z))) y=
      d*((b*Real.exp y)^2*deriv (deriv f) (b*Real.exp y)+(b*Real.exp y)*deriv f (b*Real.exp y)) := by
  let g := fun z => b*Real.exp z
  have hg z : HasDerivAt g (b*Real.exp z) z := (Real.hasDerivAt_exp z).const_mul b
  have hd : DifferentiableAt ℝ f (g y) := hf.differentiableAt (by norm_num)
  have he : deriv (fun z => d*f (g z)) y=d*g y*deriv f (g y) := by
    have hh : deriv (fun z => d*f (g z)) y=d*(deriv f (g y)*(b*Real.exp y)) := ((hd.hasDerivAt.comp y (hg y)).const_mul d).deriv
    rw [hh]
    ring
  refine ⟨he,?_⟩
  have hfd : DifferentiableAt ℝ (deriv f) (g y) :=
    (hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hfnear : ∀ᶠ x in 𝓝 (g y),DifferentiableAt ℝ f x :=
    (hf.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  have hnear : deriv (fun z => d*f (g z))=ᶠ[𝓝 y] fun z => d*g z*deriv f (g z) := by
    filter_upwards [(hg y).continuousAt.tendsto.eventually hfnear] with z hz
    have hh : deriv (fun q => d*f (g q)) z=d*(deriv f (g z)*(b*Real.exp z)) := ((hz.hasDerivAt.comp z (hg z)).const_mul d).deriv
    rw [hh]
    ring
  rw [hnear.deriv_eq]
  have hh := ((hg y).const_mul d).mul (hfd.hasDerivAt.comp y (hg y))
  have hh' : deriv (fun z => d*g z*deriv f (g z)) y=
      d*(b*Real.exp y)*deriv f (g y)+d*g y*(deriv (deriv f) (g y)*(b*Real.exp y)) := hh.deriv
  rw [hh']
  dsimp only [g]
  ring

/-- The time derivative after restarting at t0 and discounting. -/
theorem discount_shift_time_derivative (u : ℝ → ℝ) (t0 r s : ℝ)
    (hu : DifferentiableAt ℝ u (t0+s)) :
    HasDerivAt (fun q => Real.exp (-r*q)*u (t0+q))
      (Real.exp (-r*s)*(deriv u (t0+s)-r*u (t0+s))) s := by
  have hh := ((Real.hasDerivAt_exp (-r*s)).comp s ((hasDerivAt_id s).const_mul (-r))).mul
    (hu.hasDerivAt.comp s ((hasDerivAt_id s).const_add t0))
  change HasDerivAt (fun q => Real.exp (-r*q)*u (t0+q))
    (Real.exp (-r*s)*(-r*1)*u (t0+s)+Real.exp (-r*s)*(deriv u (t0+s)*1)) s at hh
  convert hh using 1 <;> ring

/-- The Black--Scholes equation becomes the constant-coefficient harmonic
 equation for the discounted value in log coordinates. -/
theorem discounted_log_generator_algebra (e x u ut ux uxx r σ : ℝ)
    (hpde : ut+r*x*ux+σ^2*x^2/2*uxx-r*u=0) :
    e*(ut-r*u)+(e*x*ux)*(r-σ^2/2)+(e*(x^2*uxx+x*ux))*σ^2/2=0 := by
  linear_combination e*hpde

end Asakura.Chapter11
