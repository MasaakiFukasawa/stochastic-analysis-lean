import Chapter5ColeHopfClosedEndpoint

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 6000000

/-- All analytic data for both applications of nonlinear Feynman--Kac
are constructed from the printed C_b^infinity primitive. The PDEs hold
at time zero for the same open-neighborhood extensions. -/
theorem bounded_smooth_burgers_closed_data (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (B : ℕ → ℝ) (hb : ∀ n x,‖iteratedDeriv n f x‖≤B n)
    (a : ℝ) (ha : a≠0) :
    ∃ O : Set (ℝ × ℝ),∃ w v : ℝ × ℝ → ℝ,
      IsOpen O ∧ {p : ℝ × ℝ | 0≤p.1} ⊆ O ∧
      ContDiffOn ℝ 3 w O ∧ ContDiffOn ℝ 2 v O ∧
      (∀ t x,0≤t → w (t,x)=logHeat a (fun y => Real.exp (a*f y)) x t) ∧
      (∀ t x,0≤t → v (t,x)=heatRatio a (fun y => Real.exp (a*f y))
        (fun y => a*deriv f y*Real.exp (a*f y)) x t) ∧
      (∀ t x,0≤t → deriv (fun y => w (t,y)) x=v (t,x)) ∧
      (∀ x,w (0,x)=f x ∧ v (0,x)=deriv f x) ∧
      (∀ t x,0≤t → deriv (fun r => w (r,x)) t=
        deriv (fun y => deriv (fun z => w (t,z)) y) x/2+a/2*(v (t,x))^2) ∧
      (∀ t x,0≤t → deriv (fun r => v (r,x)) t=
        deriv (fun y => deriv (fun z => v (t,z)) y) x/2+a*v (t,x)*deriv (fun y => v (t,y)) x) := by
  let h := fun n => iteratedDeriv n (fun y => Real.exp (a*f y))
  have he : ContDiff ℝ ∞ (fun y => Real.exp (a*f y)) := (contDiff_const.mul hf).exp
  have hd (n : ℕ) (x : ℝ) : HasDerivAt (h n) (h (n+1) x) x := by
    simpa only [h,iteratedDeriv_succ] using
      ((he.of_le (show ((n+1 : ℕ) : ℕ∞ω)≤∞ by simp)).differentiable_iteratedDeriv' n x).hasDerivAt
  choose C hC hCb using bounded_smooth_exponential_derivatives f hf B hb a
  have hCb' : ∀ n x,‖h n x‖≤C n := fun n => hCb n
  have hbf : ∀ x,|f x|≤B 0 := fun x => by simpa only [iteratedDeriv_zero,Real.norm_eq_abs] using hb 0 x
  let c := Real.exp (-|a| * B 0)
  have hc : 0<c := Real.exp_pos _
  have hpos : ∀ x,c≤h 0 x := fun x => (exponential_payoff_bounds f (B 0) a hbf x).1
  let Q := heatTaylorJet h 0 0
  let O := {p | 0<Q p}
  let w := fun p => Real.log (Q p)/a
  let v := fun p => heatTaylorJet h 0 1 p/(a*Q p)
  have hQ : ContDiff ℝ 3 Q := heatTaylorJet_contDiff h hd C hCb' 3 0 0 (by omega)
  have hQ1 : ContDiff ℝ 2 (heatTaylorJet h 0 1) := heatTaylorJet_contDiff h hd C hCb' 2 0 1 (by omega)
  have hO : IsOpen O := isOpen_lt continuous_const hQ.continuous
  have hstrip : {p : ℝ × ℝ | 0≤p.1} ⊆ O := by
    intro p hp
    change 0<heatTaylorJet h 0 0 p
    rcases p with ⟨t,x⟩
    change 0≤t at hp
    simpa only [heatTaylorJet,hp,ite_true,pow_zero,one_mul,Nat.mul_zero,Nat.zero_add] using
      hc.trans_le (heatAverage_lower_bound (h 0) he.continuous (C 0) c (hCb' 0) hpos x t)
  have hw : ContDiffOn ℝ 3 w O := (hQ.contDiffOn.log (fun p hp => ne_of_gt hp)).div_const a
  have hv : ContDiffOn ℝ 2 v O := hQ1.contDiffOn.div
    (contDiffOn_const.mul (hQ.of_le (by norm_num)).contDiffOn) (fun p hp => mul_ne_zero ha (ne_of_gt hp))
  have hwx (t x : ℝ) (ht : 0≤t) : deriv (fun y => w (t,y)) x=v (t,x) :=
    (coleHopf_derivative a x _ (fun y => Q (t,y)) (heatTaylorJet_space h hd C hCb' 0 0 t x)
      (ne_of_gt (hstrip ht))).deriv
  have hh1 x : h 1 x=a*deriv f x*Real.exp (a*f x) := by
    simp only [h,iteratedDeriv_one]
    change deriv (fun y => Real.exp (a*f y)) x=_
    rw [(((hf.differentiable (by simp) x).hasDerivAt.const_mul a).exp).deriv]
    ring
  refine ⟨O,w,v,hO,hstrip,hw,hv,?_,?_,hwx,?_,?_,?_⟩
  · intro t x ht
    simp only [w,Q,heatTaylorJet,ht,ite_true,pow_zero,one_mul,h,iteratedDeriv_zero,Nat.mul_zero,Nat.zero_add,logHeat]
  · intro t x ht
    simp only [v,Q,heatTaylorJet,ht,ite_true,pow_zero,one_mul,Nat.mul_zero,Nat.zero_add,heatRatio]
    rw [show h 0=(fun y => Real.exp (a*f y)) from rfl,show h 1=(fun y => a*deriv f y*Real.exp (a*f y)) from funext hh1]
  · intro x
    constructor
    · change Real.log (heatTaylorJet h 0 0 (0,x))/a=f x
      simpa [heatTaylorJet,h,heatAverage_zero] using coleHopf_terminal a (f x) ha
    · change heatTaylorJet h 0 1 (0,x)/(a*heatTaylorJet h 0 0 (0,x))=deriv f x
      simp only [heatTaylorJet,le_refl,ite_true,pow_zero,one_mul,Nat.mul_zero,Nat.zero_add,heatAverage_zero]
      rw [hh1]
      change (a*deriv f x*Real.exp (a*f x))/(a*Real.exp (a*f x))=deriv f x
      field_simp
  · intro t x ht
    have hp := heatTaylorLog_pde h hd C hCb' c a hc hpos ha x t ht
    change deriv (fun r => w (r,x)) t=deriv (fun y => deriv (fun z => w (t,z)) y) x/2+a/2*(deriv (fun y => w (t,y)) x)^2 at hp
    rwa [hwx t x ht] at hp
  · intro t x ht
    exact heatTaylorRatio_burgers h hd C hCb' c a hc hpos ha x t ht

end Asakura.Chapter5
