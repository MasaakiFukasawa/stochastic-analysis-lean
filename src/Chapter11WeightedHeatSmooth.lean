import Chapter11WeightedHeatKernel
import Chapter9PartialJets
import Chapter9SmoothMixtureCriterion

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Asakura.Chapter11
open Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem weighted_heat_joint_smooth (L : ℝ) (q : ℝ × (ℝ × ℝ))
    (hq : 0<q.2.1 ∧ q.2.1<L) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Real.exp (weightedHeatExponent L p.1 p.2)) q := by
  dsimp only [weightedHeatExponent]
  apply ContDiffAt.exp
  apply ContDiffAt.add
  · apply ContDiffAt.sub
    · apply contDiffAt_const.mul
      exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => 2*Real.pi*p.2.1) q).log
        (by have hh := hq.1;positivity)
    · exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (p.2.2-p.1)^2) q).div
        (by fun_prop) (by have hh := hq.1;positivity)
  · fun_prop

theorem weighted_heat_jets_continuous (L : ℝ) (n : ℕ) (z : ℝ × ℝ) (hz : 0<z.1 ∧ z.1<L) :
    Continuous (fun x : ℝ => iteratedFDerivWithin ℝ n
      (fun q => Real.exp (weightedHeatExponent L x q)) {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} z) := by
  have hU : IsOpen {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} := (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have he x : iteratedFDerivWithin ℝ n (fun q => Real.exp (weightedHeatExponent L x q)) {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} z=
      iteratedFDeriv ℝ n (fun q => Real.exp (weightedHeatExponent L x q)) z :=
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      (((weighted_heat_exponent_smooth L x).exp.contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast le_top)) hz
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro x
  have hh := joint_partial_jets_smooth
    {q : ℝ × (ℝ × ℝ) | 0<q.2.1 ∧ q.2.1<L}
    (fun q => Real.exp (weightedHeatExponent L q.1 q.2))
    (fun q hq => weighted_heat_joint_smooth L q hq) n (x,z) hz
  exact (hh.comp (g := fun q : (ℝ) × (ℝ × (ℝ)) =>
    iteratedFDeriv ℝ n (fun y => Real.exp (weightedHeatExponent L q.1 y)) q.2) x
    (show ContDiffAt ℝ ∞ (fun w : ℝ => (w,z)) x by fun_prop)).continuousAt

/-- The finite-measure weighted heat mixture is jointly smooth. -/
theorem weighted_heat_mixture_smooth (L : ℝ) (hL : 0<L) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ) => ∫ x,Real.exp (weightedHeatExponent L x z) ∂μ)
      {z : ℝ × ℝ | 0<z.1 ∧ z.1<L} := by
  let U : Set (ℝ × (ℝ)) := {z : ℝ × ℝ | 0<z.1 ∧ z.1<L}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  intro z hz
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let K := Metric.closedBall z (r/2)
  let V := Metric.ball z (r/2)
  have hKU : K ⊆ U := (Metric.closedBall_subset_ball (by linarith : r/2<r)).trans hrU
  have hVK : V ⊆ K := Metric.ball_subset_closedBall
  have hVU : V ⊆ U := hVK.trans hKU
  have hb := fun n => weighted_heat_all_order_bound L hL K (isCompact_closedBall _ _) hKU n
  choose B hB hbound using hb
  let J := fun x : ℝ => ftaylorSeriesWithin ℝ (fun q => Real.exp (weightedHeatExponent L x q)) U
  have hJ x : HasFTaylorSeriesUpToOn ∞ (fun q => Real.exp (weightedHeatExponent L x q)) (J x) V :=
    (((weighted_heat_exponent_smooth L x).exp).ftaylorSeriesWithin hU.uniqueDiffOn).mono hVU
  have hsm : ContDiffOn ℝ ∞ (fun q => ∫ x,Real.exp (weightedHeatExponent L x q) ∂μ) V := by
    apply smooth_mixture_criterion μ V Metric.isOpen_ball (fun q x => Real.exp (weightedHeatExponent L x q)) J hJ
      (fun n q hq => (weighted_heat_jets_continuous L n q (hVU hq)).aestronglyMeasurable) B
    intro n x q hq
    exact hbound n x q (hVK hq)
  exact (hsm.contDiffAt (Metric.ball_mem_nhds z (by linarith : 0<r/2))).contDiffWithinAt

/-- Every actual joint derivative can be brought inside the mixture integral. -/
theorem weighted_heat_mixture_derivative (L : ℝ) (hL : 0<L) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (z : ℝ × (ℝ)) (hz : 0<z.1 ∧ z.1<L) :
    iteratedFDerivWithin ℝ n (fun q : ℝ × (ℝ) => ∫ x,Real.exp (weightedHeatExponent L x q) ∂μ)
      {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} z =
      ∫ x,iteratedFDerivWithin ℝ n (fun q => Real.exp (weightedHeatExponent L x q)) {q : ℝ × ℝ | 0<q.1 ∧ q.1<L} z ∂μ := by
  let U : Set (ℝ × (ℝ)) := {z : ℝ × ℝ | 0<z.1 ∧ z.1<L}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let K := Metric.closedBall z (r/2)
  let V := Metric.ball z (r/2)
  have hKU : K ⊆ U := (Metric.closedBall_subset_ball (by linarith : r/2<r)).trans hrU
  have hVK : V ⊆ K := Metric.ball_subset_closedBall
  have hVU : V ⊆ U := hVK.trans hKU
  have hb := fun n => weighted_heat_all_order_bound L hL K (isCompact_closedBall _ _) hKU n
  choose B hB hbound using hb
  let J := fun x : ℝ => ftaylorSeriesWithin ℝ (fun q => Real.exp (weightedHeatExponent L x q)) U
  have hJ x : HasFTaylorSeriesUpToOn ∞ (fun q => Real.exp (weightedHeatExponent L x q)) (J x) V :=
    (((weighted_heat_exponent_smooth L x).exp).ftaylorSeriesWithin hU.uniqueDiffOn).mono hVU
  have ht := smooth_mixture_taylor μ V Metric.isOpen_ball
    (fun q x => Real.exp (weightedHeatExponent L x q)) J hJ
    (fun n q hq => (weighted_heat_jets_continuous L n q (hVU hq)).aestronglyMeasurable) B
    (fun n x q hq => hbound n x q (hVK hq))
  have hzV : z∈V := Metric.mem_ball_self (by linarith : 0<r/2)
  have he := ht.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (m := n) (by exact_mod_cast le_top) Metric.isOpen_ball.uniqueDiffOn hzV
  rw [iteratedFDerivWithin_of_isOpen n Metric.isOpen_ball hzV] at he
  rw [iteratedFDerivWithin_of_isOpen n hU hz]
  exact he.symm
end Asakura.Chapter11
