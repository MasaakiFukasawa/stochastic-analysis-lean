import Chapter5HeatTaylorJets

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 5000000

lemma heatTaylorNegative_space (h : ℕ → ℝ → ℝ)
    (hd : ∀ k x,HasDerivAt (h k) (h (k+1) x) x) (j k : ℕ) (t x : ℝ) :
    HasDerivAt (fun y => heatTaylorNegative h j k (t,y)) (heatTaylorNegative h j (k+1) (t,x)) x := by
  cases j with
  | zero =>
    convert (((hd k x).add ((hd (k+2) x).const_mul (t/2))).add
      ((hd (k+4) x).const_mul (t^2/8))).add ((hd (k+6) x).const_mul (t^3/48)) using 1 <;> (try funext y) <;>
      simp [heatTaylorNegative,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | succ j => cases j with
    | zero =>
      convert (((hd (k+2) x).div_const 2).add ((hd (k+4) x).const_mul (t/4))).add
        ((hd (k+6) x).const_mul (t^2/16)) using 1 <;> (try funext y) <;>
        simp [heatTaylorNegative,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    | succ j => cases j with
      | zero =>
        convert ((hd (k+4) x).div_const 4).add ((hd (k+6) x).const_mul (t/8)) using 1 <;> (try funext y) <;>
          simp [heatTaylorNegative,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      | succ j =>
        convert (hd (k+6) x).div_const 8 using 1 <;> (try funext y) <;>
          simp [heatTaylorNegative,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

lemma heatTaylorNegative_time (h : ℕ → ℝ → ℝ) (j k : ℕ) (hj : j<3) (t x : ℝ) :
    HasDerivAt (fun s => heatTaylorNegative h j k (s,x)) (heatTaylorNegative h (j+1) k (t,x)) t := by
  have h1 := hasDerivAt_id t
  interval_cases j
  · convert (((hasDerivAt_const t (h k x)).add ((h1.div_const 2).mul_const (h (k+2) x))).add
      (((h1.pow 2).div_const 8).mul_const (h (k+4) x))).add
      (((h1.pow 3).div_const 48).mul_const (h (k+6) x)) using 1 <;> (try funext y) <;>
      norm_num [heatTaylorNegative,Pi.add_apply,id_eq] <;> ring
  · convert ((hasDerivAt_const t (h (k+2) x/2)).add ((h1.div_const 4).mul_const (h (k+4) x))).add
      (((h1.pow 2).div_const 16).mul_const (h (k+6) x)) using 1 <;> (try funext y) <;>
      norm_num [heatTaylorNegative,Pi.add_apply,id_eq] <;> ring
  · convert (hasDerivAt_const t (h (k+4) x/4)).add ((h1.div_const 8).mul_const (h (k+6) x)) using 1 <;> (try funext y) <;>
      norm_num [heatTaylorNegative,Pi.add_apply,id_eq] <;> ring

/-- All space derivatives match across the time boundary, including at
zero itself, where the formula is exactly the original datum. -/
theorem heatTaylorJet_space (h : ℕ → ℝ → ℝ)
    (hd : ∀ k x,HasDerivAt (h k) (h (k+1) x) x)
    (B : ℕ → ℝ) (hb : ∀ k x,‖h k x‖≤B k) (j k : ℕ) (t x : ℝ) :
    HasDerivAt (fun y => heatTaylorJet h j k (t,y)) (heatTaylorJet h j (k+1) (t,x)) x := by
  have hc k : Continuous (h k) := continuous_iff_continuousAt.mpr (fun x => (hd k x).continuousAt)
  by_cases ht : 0≤t
  · simpa only [heatTaylorJet,ht,ite_true,Nat.add_assoc] using
      (heatAverage_space_derivative (hd (2*j+k)) (hc _) (B _) (B _) (hb _) (hb _) x t).const_mul ((1/2:ℝ)^j)
  · simpa only [heatTaylorJet,ht,ite_false] using heatTaylorNegative_space h hd j k t x

/-- Time differentiability at zero is proved from the matching continuous
derivatives, not presumed from the positive-time heat equation. -/
theorem heatTaylorJet_time (h : ℕ → ℝ → ℝ)
    (hd : ∀ k x,HasDerivAt (h k) (h (k+1) x) x)
    (B : ℕ → ℝ) (hb : ∀ k x,‖h k x‖≤B k) (j k : ℕ) (hj : j<3) (t x : ℝ) :
    HasDerivAt (fun s => heatTaylorJet h j k (s,x)) (heatTaylorJet h (j+1) k (t,x)) t := by
  have hc k : Continuous (h k) := continuous_iff_continuousAt.mpr (fun x => (hd k x).continuousAt)
  have hn (s : ℝ) (hs : s≠0) : HasDerivAt (fun r => heatTaylorJet h j k (r,x))
      (heatTaylorJet h (j+1) k (s,x)) s := by
    rcases lt_or_gt_of_ne hs with hs|hs
    · have he : (fun r => heatTaylorJet h j k (r,x)) =ᶠ[𝓝 s] fun r => heatTaylorNegative h j k (r,x) := by
        filter_upwards [Iio_mem_nhds hs] with r hr
        change r<0 at hr
        simp only [heatTaylorJet,not_le.mpr hr,ite_false]
      simpa only [heatTaylorJet,not_le.mpr hs,ite_false] using
        (heatTaylorNegative_time h j k hj s x).congr_of_eventuallyEq he
    · have he : (fun r => heatTaylorJet h j k (r,x)) =ᶠ[𝓝 s]
          fun r => (1/2:ℝ)^j*heatAverage (h (2*j+k)) x r := by
        filter_upwards [Ioi_mem_nhds hs] with r hr
        change 0<r at hr
        simp only [heatTaylorJet,hr.le,ite_true]
      have hh := (heatAverage_heat_equation (hd (2*j+k)) (hd (2*j+k+1)) (hc _)
        (B _) (B _) (B _) (hb _) (hb _) (hb _) x s hs).const_mul ((1/2:ℝ)^j)
      have heval : heatTaylorJet h (j+1) k (s,x)=
          (1/2:ℝ)^j*((1/2)*heatAverage (h (2*j+k+1+1)) x s) := by
        simp only [heatTaylorJet,hs.le,ite_true,pow_succ]
        have heidx : 2*(j+1)+k=2*j+k+1+1 := by omega
        rw [heidx]; ring
      rw [heval]
      exact hh.congr_of_eventuallyEq he
  by_cases ht : t=0
  · subst t
    exact derivative_across_zero _ _
      ((heatTaylorJet_continuous h hc B hb j k hj.le).comp (continuous_id.prodMk continuous_const)).continuousAt
      ((heatTaylorJet_continuous h hc B hb (j+1) k (by omega)).comp (continuous_id.prodMk continuous_const)).continuousAt hn
  · exact hn t ht

end Asakura.Chapter5
