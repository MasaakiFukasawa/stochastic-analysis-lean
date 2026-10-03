import Chapter5BurgersClosedEndpoint

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 5000000

/-- Logarithmic heat PDE for the actual open-neighborhood extension,
including time zero. -/
theorem heatTaylorLog_pde (h : ℕ → ℝ → ℝ)
    (hd : ∀ k x,HasDerivAt (h k) (h (k+1) x) x)
    (B : ℕ → ℝ) (hb : ∀ k x,‖h k x‖≤B k)
    (c a : ℝ) (hc : 0<c) (hpos : ∀ x,c≤h 0 x) (ha : a≠0)
    (x t : ℝ) (ht : 0≤t) :
    let w := fun t x => Real.log (heatTaylorJet h 0 0 (t,x))/a
    deriv (fun r => w r x) t =
      deriv (fun y => deriv (fun z => w t z) y) x/2+a/2*(deriv (fun y => w t y) x)^2 := by
  dsimp only
  let Q := heatTaylorJet h 0 0
  have hcg : Continuous (h 0) := continuous_iff_continuousAt.mpr (fun y => (hd 0 y).continuousAt)
  have hq y : 0<Q (t,y) := by
    simpa only [Q,heatTaylorJet,ht,ite_true,pow_zero,one_mul,Nat.mul_zero,Nat.zero_add] using
      hc.trans_le (heatAverage_lower_bound (h 0) hcg (B 0) c (hb 0) hpos y t)
  have h0 y := heatTaylorJet_space h hd B hb 0 0 t y
  have h1 y := heatTaylorJet_space h hd B hb 0 1 t y
  have hw y : HasDerivAt (fun z => (Real.log (Q (t,z))/a))
      (heatTaylorJet h 0 1 (t,y)/(a*Q (t,y))) y := by
    exact coleHopf_derivative a y (heatTaylorJet h 0 1 (t,y)) (fun z => Q (t,z)) (h0 y) (hq y).ne'
  have he : (fun y => deriv (fun z => (Real.log (Q (t,z))/a)) y) =
      (fun y => heatTaylorJet h 0 1 (t,y)/(a*Q (t,y))) := by
    funext y;exact (hw y).deriv
  have hv : HasDerivAt (fun y => heatTaylorJet h 0 1 (t,y)/(a*Q (t,y)))
      ((heatTaylorJet h 0 2 (t,x)*Q (t,x)-(heatTaylorJet h 0 1 (t,x))^2)/
        (a*(Q (t,x))^2)) x := by
    convert (h1 x).div ((h0 x).const_mul a) (mul_ne_zero ha (hq x).ne') using 1
    field_simp
    <;> ring
  have htime : HasDerivAt (fun r => Q (r,x)) ((1/2)*heatTaylorJet h 0 2 (t,x)) t := by
    convert heatTaylorJet_time h hd B hb 0 0 (by norm_num) t x using 1
    norm_num [heatTaylorJet,ht]
  have hwt : HasDerivAt (fun r => Real.log (Q (r,x))/a)
      (((1/2)*heatTaylorJet h 0 2 (t,x))/(a*Q (t,x))) t :=
    coleHopf_derivative a t _ (fun r => Q (r,x)) htime (hq x).ne'
  rw [hwt.deriv,he,hv.deriv,(hw x).deriv]
  have hne := (hq x).ne'
  field_simp
  <;> ring

end Asakura.Chapter5
