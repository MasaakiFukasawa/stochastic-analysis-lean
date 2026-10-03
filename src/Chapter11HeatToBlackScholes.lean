import Chapter11PayoffHeatPDE
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

noncomputable def heatPrice (F : ℝ × ℝ → ℝ) (r σ θ x : ℝ) : ℝ :=
  Real.exp (-r*θ)*F (σ^2*θ,Real.log x+(r-σ^2/2)*θ)

theorem heat_price_dx (F : ℝ × ℝ → ℝ) (r σ θ x : ℝ) (hx : 0<x)
    (hF : ContDiff ℝ ∞ (fun y => F (σ^2*θ,y))) :
    HasDerivAt (heatPrice F r σ θ)
      (Real.exp (-r*θ)*deriv (fun y => F (σ^2*θ,y)) (Real.log x+(r-σ^2/2)*θ)/x) x := by
  have hh := ((hF.differentiable (by simp)).differentiableAt.hasDerivAt.comp x
    ((Real.hasDerivAt_log hx.ne').add_const ((r-σ^2/2)*θ))).const_mul (Real.exp (-r*θ))
  convert hh using 1
  · rfl
  · ring

theorem heat_price_dxx (F : ℝ × ℝ → ℝ) (r σ θ x : ℝ) (hx : 0<x)
    (hF : ContDiff ℝ ∞ (fun y => F (σ^2*θ,y))) :
    HasDerivAt (deriv (heatPrice F r σ θ))
      (Real.exp (-r*θ)*(deriv (deriv (fun y => F (σ^2*θ,y))) (Real.log x+(r-σ^2/2)*θ)-
        deriv (fun y => F (σ^2*θ,y)) (Real.log x+(r-σ^2/2)*θ))/x^2) x := by
  have hd := (((contDiff_infty_iff_deriv.mp hF).2.differentiable (by simp)).differentiableAt.hasDerivAt.comp x
    ((Real.hasDerivAt_log hx.ne').add_const ((r-σ^2/2)*θ))).const_mul (Real.exp (-r*θ))
  have hh := hd.div (hasDerivAt_id x) hx.ne'
  apply HasDerivAt.congr_of_eventuallyEq (by convert hh using 1 <;> first | rfl | (simp only [Function.comp_def,id_eq];field_simp <;> ring))
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact (heat_price_dx F r σ θ y hy hF).deriv

/-- The logarithmic change of variables converts the actual heat equation
into the Black--Scholes equation; every derivative here is an actual deriv. -/
theorem heat_price_equation (F : ℝ × ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F {q | 0<q.1})
    (hHeat : ∀ t y,0<t → deriv (fun s => F (s,y)) t=(1/2:ℝ)*deriv (deriv (fun a => F (t,a))) y)
    (r σ θ x : ℝ) (hσ : σ≠0) (hθ : 0<θ) (hx : 0<x) :
    deriv (fun s => heatPrice F r σ s x) θ=
      r*x*deriv (heatPrice F r σ θ) x+σ^2*x^2/2*deriv (deriv (heatPrice F r σ θ)) x-r*heatPrice F r σ θ x := by
  let t := σ^2*θ
  let y := Real.log x+(r-σ^2/2)*θ
  have ht : 0<t := mul_pos (sq_pos_of_ne_zero hσ) hθ
  have hFa a : ContDiffAt ℝ ∞ F (t,a) := hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  have hs : ContDiff ℝ ∞ (fun a => F (t,a)) := by
    rw [contDiff_iff_contDiffAt]
    intro a
    exact (hFa a).comp a (contDiffAt_const.prodMk contDiffAt_id)
  have hft : fderiv ℝ F (t,y) (1,0)=deriv (fun s => F (s,y)) t := by
    simpa only [iteratedFDeriv_one_apply] using (scalar_time_slice_derivative F t y (hFa y)).deriv.symm
  have hfy : fderiv ℝ F (t,y) (0,1)=deriv (fun a => F (t,a)) y := by
    simpa only [iteratedFDeriv_one_apply] using (scalar_space_slice_derivative F t y (hFa y)).deriv.symm
  have hd := ((hFa y).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt θ
    (((hasDerivAt_id θ).const_mul (σ^2)).prodMk (((hasDerivAt_id θ).const_mul (r-σ^2/2)).const_add (Real.log x)))
  have he : (σ^2,r-σ^2/2)=(σ^2) • (1,0)+(r-σ^2/2) • (0,1) := by ext <;> simp
  simp only [Function.comp_def,mul_one,one_mul] at hd
  rw [he,map_add,map_smul,map_smul,hft,hfy,hHeat t y ht] at hd
  have hE := ((hasDerivAt_id θ).const_mul (-r)).exp
  have hprice := hE.mul hd
  have htime : deriv (fun s => heatPrice F r σ s x) θ=
      (-r*Real.exp (-r*θ))*F (t,y)+Real.exp (-r*θ)*
        (σ^2*((1/2:ℝ)*deriv (deriv (fun a => F (t,a))) y)+(r-σ^2/2)*deriv (fun a => F (t,a)) y) := by
    convert hprice.deriv using 1 <;> first | rfl | (simp only [smul_eq_mul,id_eq,t,y];ring)
  rw [htime,(heat_price_dx F r σ θ x hx hs).deriv,(heat_price_dxx F r σ θ x hx hs).deriv]
  dsimp only [heatPrice,t,y]
  field_simp
  <;> ring

theorem heat_price_joint_smooth (F : ℝ × ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F {q | 0<q.1}) (r σ θ x : ℝ)
    (hσ : σ≠0) (hθ : 0<θ) (hx : 0<x) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => heatPrice F r σ q.1 q.2) (θ,x) := by
  have hlog : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => Real.log q.2) (θ,x) := contDiffAt_snd.log hx.ne'
  have hmap : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (σ^2*q.1,Real.log q.2+(r-σ^2/2)*q.1)) (θ,x) :=
    (contDiffAt_const.mul contDiffAt_fst).prodMk (hlog.add (contDiffAt_const.mul contDiffAt_fst))
  have hh := (hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds
    (mul_pos (sq_pos_of_ne_zero hσ) hθ))).comp (θ,x) hmap
  exact ((contDiffAt_const.mul contDiffAt_fst).exp).mul hh

theorem heat_price_backward_equation (F : ℝ × ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F {q | 0<q.1})
    (hHeat : ∀ t y,0<t → deriv (fun s => F (s,y)) t=(1/2:ℝ)*deriv (deriv (fun a => F (t,a))) y)
    (r σ T t x : ℝ) (hσ : σ≠0) (ht : t<T) (hx : 0<x) :
    deriv (fun s => heatPrice F r σ (T-s) x) t+
      r*x*deriv (heatPrice F r σ (T-t)) x+
      σ^2*x^2/2*deriv (deriv (heatPrice F r σ (T-t))) x-r*heatPrice F r σ (T-t) x=0 := by
  have hs := heat_price_joint_smooth F hF r σ (T-t) x hσ (sub_pos.mpr ht) hx
  have htime : DifferentiableAt ℝ (fun a => heatPrice F r σ a x) (T-t) :=
    ((hs.comp (T-t) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  have hd := htime.hasDerivAt.comp t ((hasDerivAt_const t T).sub (hasDerivAt_id t))
  have he : deriv (fun s => heatPrice F r σ (T-s) x) t= -deriv (fun s => heatPrice F r σ s x) (T-t) := by
    simpa only [Function.comp_def,Pi.sub_apply,id_eq,zero_sub,mul_neg_one] using hd.deriv
  rw [he,heat_price_equation F hF hHeat r σ (T-t) x hσ (sub_pos.mpr ht) hx]
  ring

end Asakura.Chapter11
