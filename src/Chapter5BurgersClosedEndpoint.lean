import Chapter5BurgersOpenRegularity
import Chapter5BurgersHeat

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 5000000

/-- The actual Taylor extension satisfies Burgers' PDE also at time zero.
Its time derivative here is the two-sided derivative of the C² extension. -/
theorem heatTaylorRatio_burgers (h : ℕ → ℝ → ℝ)
    (hd : ∀ k x,HasDerivAt (h k) (h (k+1) x) x)
    (B : ℕ → ℝ) (hb : ∀ k x,‖h k x‖≤B k)
    (c a : ℝ) (hc : 0<c) (hpos : ∀ x,c≤h 0 x) (ha : a≠0)
    (x t : ℝ) (ht : 0≤t) :
    let v := fun t x => heatTaylorJet h 0 1 (t,x)/(a*heatTaylorJet h 0 0 (t,x))
    deriv (fun r => v r x) t =
      deriv (fun y => deriv (fun z => v t z) y) x/2+a*v t x*deriv (fun y => v t y) x := by
  dsimp only
  have hcg : Continuous (h 0) := continuous_iff_continuousAt.mpr (fun y => (hd 0 y).continuousAt)
  let q := fun y => heatTaylorJet h 0 0 (t,y)
  let r := fun y => heatTaylorJet h 0 1 (t,y)
  let s := fun y => heatTaylorJet h 0 2 (t,y)
  let u := fun y => heatTaylorJet h 0 3 (t,y)
  have hq y : q y ≠ 0 := by
    change heatTaylorJet h 0 0 (t,y)≠0
    simpa only [heatTaylorJet,ht,ite_true,pow_zero,one_mul,Nat.mul_zero,Nat.zero_add] using
      (hc.trans_le (heatAverage_lower_bound (h 0) hcg (B 0) c (hb 0) hpos y t)).ne'
  have h0 y : HasDerivAt q (r y) y := heatTaylorJet_space h hd B hb 0 0 t y
  have h1 y : HasDerivAt r (s y) y := heatTaylorJet_space h hd B hb 0 1 t y
  have h2 y : HasDerivAt s (u y) y := heatTaylorJet_space h hd B hb 0 2 t y
  have hv y : HasDerivAt (fun z => (heatTaylorJet h 0 1 (t,z)/(a*heatTaylorJet h 0 0 (t,z))))
      (s y/(a*q y)-(r y)^2/(a*(q y)^2)) y := by
    convert (h1 y).div ((h0 y).const_mul a) (mul_ne_zero ha (hq y)) using 1
    field_simp <;> ring
  have hvfun : (fun y => deriv (fun z => (heatTaylorJet h 0 1 (t,z)/(a*heatTaylorJet h 0 0 (t,z)))) y) =
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
  have ht0 : HasDerivAt (fun r => heatTaylorJet h 0 0 (r,x)) (s x/2) t := by
    convert heatTaylorJet_time h hd B hb 0 0 (by norm_num) t x using 1
    norm_num [s,heatTaylorJet,ht]; ring
  have ht1 : HasDerivAt (fun r => heatTaylorJet h 0 1 (r,x)) (u x/2) t := by
    convert heatTaylorJet_time h hd B hb 0 1 (by norm_num) t x using 1
    norm_num [u,heatTaylorJet,ht]; ring
  have hvt : HasDerivAt (fun r => heatTaylorJet h 0 1 (r,x)/(a*heatTaylorJet h 0 0 (r,x)))
      ((u x*q x-r x*s x)/(2*a*(q x)^2)) t := by
    convert ht1.div (ht0.const_mul a) (mul_ne_zero ha (hq x)) using 1
    change (u x*q x-r x*s x)/(2*a*(q x)^2) = _
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
