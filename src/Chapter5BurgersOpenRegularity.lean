import Chapter5HeatTaylorRegularity
import Chapter5BoundedSmoothExponential
import Chapter5LogHeat
import Chapter5ExponentialPayoff

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 5000000

/-- The actual bounded smooth primitive supplies a C^3 extension of its
exponential heat average. Positivity gives an open neighborhood of every
closed positive-time strip on which log(q)/a is C^3 and its space derivative
is C^2, exactly the added assumption in the revised Burgers example. -/
theorem burgers_formula_open_regular_extension (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (B : ℕ → ℝ) (hb : ∀ n x,‖iteratedDeriv n f x‖≤B n)
    (a : ℝ) :
    ∃ Q : ℝ × ℝ → ℝ,
      ContDiff ℝ 3 Q ∧
      (∀ t x,0≤t → Q (t,x)=heatAverage (fun y => Real.exp (a*f y)) x t) ∧
      (∀ t x,t<0 → Q (t,x)=
        Real.exp (a*f x)+t/2*iteratedDeriv 2 (fun y => Real.exp (a*f y)) x+
        t^2/8*iteratedDeriv 4 (fun y => Real.exp (a*f y)) x+
        t^3/48*iteratedDeriv 6 (fun y => Real.exp (a*f y)) x) ∧
      IsOpen {p | 0<Q p} ∧
      (∀ R,{p : ℝ × ℝ | p.1∈Icc 0 R} ⊆ {p | 0<Q p}) ∧
      ContDiffOn ℝ 3 (fun p => Real.log (Q p)/a) {p | 0<Q p} ∧
      ContDiffOn ℝ 2 (fun p => fderiv ℝ (fun p => Real.log (Q p)/a) p (0,1)) {p | 0<Q p} := by
  classical
  let h := fun n => iteratedDeriv n (fun y => Real.exp (a*f y))
  have he : ContDiff ℝ ∞ (fun y => Real.exp (a*f y)) := (contDiff_const.mul hf).exp
  have hd (n : ℕ) (x : ℝ) : HasDerivAt (h n) (h (n+1) x) x := by
    simpa only [h,iteratedDeriv_succ] using ((he.of_le (show ((n+1 : ℕ) : ℕ∞ω) ≤ ∞ by simp)).differentiable_iteratedDeriv' n x).hasDerivAt
  choose C hC hCb using bounded_smooth_exponential_derivatives f hf B hb a
  have hCb' : ∀ n x,‖h n x‖≤C n := fun n => hCb n
  obtain ⟨hQ,heq,hneg⟩ := heat_average_C3_Taylor_extension h hd C hCb'
  let Q := heatTaylorJet h 0 0
  have hpos (t x : ℝ) (ht : 0≤t) : 0<Q (t,x) := by
    change 0 < heatTaylorJet h 0 0 (t,x)
    rw [heq t x ht]
    have hbf : ∀ y,|f y|≤B 0 := fun y => by simpa only [iteratedDeriv_zero,Real.norm_eq_abs] using hb 0 y
    apply (Real.exp_pos (-|a| * B 0)).trans_le
    apply heatAverage_lower_bound (fun y => Real.exp (a*f y)) he.continuous
      (Real.exp (|a| * B 0)) (Real.exp (-|a| * B 0))
    · intro y; simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using (exponential_payoff_bounds f (B 0) a hbf y).2
    · intro y; exact (exponential_payoff_bounds f (B 0) a hbf y).1
  have hO : IsOpen {p | 0<Q p} := isOpen_lt continuous_const hQ.continuous
  have hw : ContDiffOn ℝ 3 (fun p => Real.log (Q p)/a) {p | 0<Q p} :=
    (hQ.contDiffOn.log (fun p hp => ne_of_gt hp)).div_const a
  refine ⟨Q,hQ,heq,?_,hO,(fun R p hp => hpos p.1 p.2 hp.1),hw,?_⟩
  · intro t x ht
    simpa only [h,iteratedDeriv_zero] using hneg t x ht
  · exact (hw.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const

end Asakura.Chapter5
