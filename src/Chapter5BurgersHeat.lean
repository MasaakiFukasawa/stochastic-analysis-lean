import Chapter5BoundedColeHopf

namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 1200000

noncomputable def heatRatio (a : ℝ) (g dg : ℝ → ℝ) (x t : ℝ) : ℝ :=
  heatAverage dg x t/(a*heatAverage g x t)

/-- The actual spatial derivative of the logarithmic heat formula solves
Burgers' PDE. Both time and second space derivatives are derived here. -/
theorem heatRatio_burgers (g dg ddg dddg : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt g (dg x) x)
    (hdd : ∀ x, HasDerivAt dg (ddg x) x)
    (hddd : ∀ x, HasDerivAt ddg (dddg x) x) (hcddd : Continuous dddg)
    (B D E G c a : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (hdg : ∀ x, ‖dg x‖ ≤ D) (hddg : ∀ x, ‖ddg x‖ ≤ E)
    (hdddg : ∀ x, ‖dddg x‖ ≤ G)
    (hc : 0 < c) (hpos : ∀ x, c ≤ g x) (ha : a ≠ 0)
    (x t : ℝ) (ht : 0 < t) :
    deriv (heatRatio a g dg x) t =
      deriv (fun y => deriv (fun z => heatRatio a g dg z t) y) x/2 +
      a*heatRatio a g dg x t*deriv (fun y => heatRatio a g dg y t) x := by
  have hcg : Continuous g := continuous_iff_continuousAt.2 (fun y => (hd y).continuousAt)
  have hcdg : Continuous dg := continuous_iff_continuousAt.2 (fun y => (hdd y).continuousAt)
  have hcddg : Continuous ddg := continuous_iff_continuousAt.2 (fun y => (hddd y).continuousAt)
  let q := fun y => heatAverage g y t
  let r := fun y => heatAverage dg y t
  let s := fun y => heatAverage ddg y t
  let u := fun y => heatAverage dddg y t
  have hq y : q y ≠ 0 := (hc.trans_le (heatAverage_lower_bound g hcg B c hg hpos y t)).ne'
  have h0 y : HasDerivAt q (r y) y := heatAverage_space_derivative hd hcdg B D hg hdg y t
  have h1 y : HasDerivAt r (s y) y := heatAverage_space_derivative hdd hcddg D E hdg hddg y t
  have h2 y : HasDerivAt s (u y) y := heatAverage_space_derivative hddd hcddd E G hddg hdddg y t
  have hv y : HasDerivAt (fun z => heatRatio a g dg z t)
      (s y/(a*q y)-(r y)^2/(a*(q y)^2)) y := by
    convert (h1 y).div ((h0 y).const_mul a) (mul_ne_zero ha (hq y)) using 1
    · rfl
    · field_simp <;> ring
  have hvfun : (fun y => deriv (fun z => heatRatio a g dg z t) y) =
      (fun y => s y/(a*q y)-(r y)^2/(a*(q y)^2)) := by
    funext y;exact (hv y).deriv
  have hvv : HasDerivAt (fun y => s y/(a*q y)-(r y)^2/(a*(q y)^2))
      ((u x/q x-3*r x*s x/(q x)^2+2*(r x)^3/(q x)^3)/a) x := by
    have hA := (h2 x).div ((h0 x).const_mul a) (mul_ne_zero ha (hq x))
    have hB := ((h1 x).pow 2).div (((h0 x).pow 2).const_mul a)
      (mul_ne_zero ha (pow_ne_zero _ (hq x)))
    convert hA.sub hB using 1
    simp only [Pi.pow_apply]
    have hx := hq x
    field_simp
    <;> ring
  have ht0 := heatAverage_heat_equation hd hdd hcddg B D E hg hdg hddg x t ht
  have ht1 := heatAverage_heat_equation hdd hddd hcddd D E G hdg hddg hdddg x t ht
  have hvt : HasDerivAt (heatRatio a g dg x)
      ((u x*q x-r x*s x)/(2*a*(q x)^2)) t := by
    convert ht1.div (ht0.const_mul a) (mul_ne_zero ha (hq x)) using 1
    · rfl
    · change (u x*q x-r x*s x)/(2*a*(q x)^2) = _
      have hx := hq x
      dsimp only [q,r,s,u]
      field_simp
      <;> ring
  rw [hvt.deriv,hvfun,hvv.deriv,(hv x).deriv]
  change (u x*q x-r x*s x)/(2*a*(q x)^2) =
    ((u x/q x-3*r x*s x/(q x)^2+2*(r x)^3/(q x)^3)/a)/2 +
    a*(r x/(a*q x))*(s x/(a*q x)-(r x)^2/(a*(q x)^2))
  have hx := hq x
  field_simp
  <;> ring

end Asakura.Chapter5
