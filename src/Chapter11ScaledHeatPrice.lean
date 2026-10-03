import Chapter11HeatToBlackScholes

open Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- A fixed change of stock units preserves the Black--Scholes PDE. -/
theorem scaled_heat_price_equation (F : ℝ × ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F {q | 0<q.1})
    (hHeat : ∀ t y,0<t → deriv (fun s => F (s,y)) t=(1/2:ℝ)*deriv (deriv (fun a => F (t,a))) y)
    (b r σ θ x : ℝ) (hb : 0<b) (hσ : σ≠0) (hθ : 0<θ) (hx : 0<x) :
    deriv (fun s => heatPrice F r σ s (x/b)) θ=
      r*x*deriv (fun y => heatPrice F r σ θ (y/b)) x+
      σ^2*x^2/2*deriv (deriv (fun y => heatPrice F r σ θ (y/b))) x-
      r*heatPrice F r σ θ (x/b) := by
  let f := heatPrice F r σ θ
  have hs y (hy : 0<y) : ContDiffAt ℝ ∞ f y :=
    (heat_price_joint_smooth F hF r σ θ y hσ hθ hy).comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hd y (hy : 0<y) : HasDerivAt (fun z => f (z/b)) (deriv f (y/b)/b) y := by
    convert ((hs (y/b) (div_pos hy hb)).differentiableAt (by simp)).hasDerivAt.comp y ((hasDerivAt_id y).div_const b) using 1 <;> first | rfl | ring
  have he : deriv (fun z => f (z/b))=ᶠ[𝓝 x] fun y => deriv f (y/b)/b := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact (hd y hy).deriv
  have hdf : DifferentiableAt ℝ (deriv f) (x/b) := by
    have hh := (hs (x/b) (div_pos hx hb)).fderiv_right (m:=1) (by simp)
    have hd' := hh.differentiableAt (by simp)
    have happ := hd'.hasFDerivAt.clm_apply (hasFDerivAt_const (c:=(1:ℝ)) (x/b))
    simpa only [fderiv_apply_one_eq_deriv] using happ.differentiableAt
  have hdd := (hdf.hasDerivAt.comp x ((hasDerivAt_id x).div_const b)).div_const b
  have hdd' : deriv (deriv (fun z => f (z/b))) x=deriv (deriv f) (x/b)/b^2 := by
    rw [he.deriv_eq]
    convert hdd.deriv using 1 <;> first | rfl | ring
  have hP := heat_price_equation F hF hHeat r σ θ (x/b) hσ hθ (div_pos hx hb)
  rw [(hd x hx).deriv,hdd']
  change deriv (fun s => heatPrice F r σ s (x/b)) θ=_
  rw [hP]
  dsimp only [f]
  field_simp
  <;> ring

end Asakura.Chapter11
