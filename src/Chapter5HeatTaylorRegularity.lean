import Chapter5HeatTaylorDerivatives

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 4500000

/-- Differentiating the explicit glued jets proves joint C^3 regularity
of the manuscript's negative-time Taylor extension. -/
theorem heatTaylorJet_contDiff (h : ℕ → ℝ → ℝ)
    (hd : ∀ k x,HasDerivAt (h k) (h (k+1) x) x)
    (B : ℕ → ℝ) (hb : ∀ k x,‖h k x‖≤B k)
    (r j k : ℕ) (hj : j+r≤3) : ContDiff ℝ r (heatTaylorJet h j k) := by
  have hc k : Continuous (h k) := continuous_iff_continuousAt.mpr (fun x => (hd k x).continuousAt)
  induction r generalizing j k with
  | zero =>
    exact contDiff_zero.mpr (heatTaylorJet_continuous h hc B hb j k (by omega))
  | succ r ih =>
    let D := fun p => heatTaylorJet h (j+1) k p • (ContinuousLinearMap.fst ℝ ℝ ℝ)+
      heatTaylorJet h j (k+1) p • (ContinuousLinearMap.snd ℝ ℝ ℝ)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨D,?_,?_⟩
    · exact ((ih (j+1) k (by omega)).smul_const _).add ((ih j (k+1) (by omega)).smul_const _)
    · intro p
      have hh := two_variable_derivative (heatTaylorJet h j k) (heatTaylorJet h (j+1) k) (heatTaylorJet h j (k+1))
        (fun t x => heatTaylorJet_time h hd B hb j k (by omega) t x)
        (fun t x => heatTaylorJet_space h hd B hb j k t x)
        (heatTaylorJet_continuous h hc B hb (j+1) k (by omega))
        (heatTaylorJet_continuous h hc B hb j (k+1) (by omega)) p
      have he : D p=(((ContinuousLinearMap.id ℝ ℝ).smulRight (heatTaylorJet h (j+1) k p)).coprod
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (heatTaylorJet h j (k+1) p))) := by
        apply ContinuousLinearMap.ext
        intro v
        simp [D,ContinuousLinearMap.coprod_apply,ContinuousLinearMap.smulRight_apply,mul_comm]
      rw [he]
      exact hh

/-- The extension equals the actual heat average for all nonnegative
times and is C^3 on the whole time-space plane. -/
theorem heat_average_C3_Taylor_extension (h : ℕ → ℝ → ℝ)
    (hd : ∀ k x,HasDerivAt (h k) (h (k+1) x) x)
    (B : ℕ → ℝ) (hb : ∀ k x,‖h k x‖≤B k) :
    ContDiff ℝ 3 (heatTaylorJet h 0 0) ∧
    (∀ t x,0≤t → heatTaylorJet h 0 0 (t,x)=heatAverage (h 0) x t) ∧
    (∀ t x,t<0 → heatTaylorJet h 0 0 (t,x)=
      h 0 x+t/2*h 2 x+t^2/8*h 4 x+t^3/48*h 6 x) := by
  refine ⟨heatTaylorJet_contDiff h hd B hb 3 0 0 (by omega),?_,?_⟩
  · intro t x ht; simp [heatTaylorJet,ht]
  · intro t x ht; simp [heatTaylorJet,not_le.mpr ht,heatTaylorNegative]

end Asakura.Chapter5
