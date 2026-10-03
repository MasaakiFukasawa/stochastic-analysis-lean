import Chapter9GaussianAllOrders
import Chapter9PartialJets
import Chapter9SmoothMixtureCriterion

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem ou_kernel_jets_continuous {d : ℕ} (n : ℕ) (z : ℝ × (Fin d → ℝ)) (hz : 0<z.1) :
    Continuous (fun x : Fin d → ℝ => iteratedFDerivWithin ℝ n
      (fun q => Real.exp (ouExponent x q)) {q | 0<q.1} z) := by
  have hU : IsOpen {q : ℝ × (Fin d → ℝ) | 0<q.1} := isOpen_lt continuous_const continuous_fst
  have he x : iteratedFDerivWithin ℝ n (fun q => Real.exp (ouExponent x q)) {q | 0<q.1} z=
      iteratedFDeriv ℝ n (fun q => Real.exp (ouExponent x q)) z :=
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      (((ou_exponent_smooth x).exp.contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast le_top)) hz
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro x
  have hh := joint_partial_jets_smooth
    {q : (Fin d → ℝ) × (ℝ × (Fin d → ℝ)) | 0<q.2.1}
    (fun q => Real.exp (ouExponent q.1 q.2))
    (fun q hq => ou_kernel_joint_smooth q.1 q.2 hq) n (x,z) hz
  exact (hh.comp (g := fun q : (Fin d → ℝ) × (ℝ × (Fin d → ℝ)) =>
    iteratedFDeriv ℝ n (fun y => Real.exp (ouExponent q.1 y)) q.2) x
    (show ContDiffAt ℝ ∞ (fun w : Fin d → ℝ => (w,z)) x by fun_prop)).continuousAt

/-- Actual OU Gaussian mixtures, including mixtures with discrete initial
laws, are jointly smooth in every positive time and every spatial variable. -/
theorem ou_gaussian_mixture_smooth {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] :
    ContDiffOn ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => ∫ x,Real.exp (ouExponent x z) ∂μ)
      {z | 0<z.1} := by
  let U : Set (ℝ × (Fin d → ℝ)) := {z | 0<z.1}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst
  intro z hz
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let K := Metric.closedBall z (r/2)
  let V := Metric.ball z (r/2)
  have hKU : K ⊆ U := (Metric.closedBall_subset_ball (by linarith : r/2<r)).trans hrU
  have hVK : V ⊆ K := Metric.ball_subset_closedBall
  have hVU : V ⊆ U := hVK.trans hKU
  have hb := fun n => ou_kernel_all_order_compact_bound K (isCompact_closedBall _ _) hKU n
  choose B hB hbound using hb
  let J := fun x : Fin d → ℝ => ftaylorSeriesWithin ℝ (fun q => Real.exp (ouExponent x q)) U
  have hJ x : HasFTaylorSeriesUpToOn ∞ (fun q => Real.exp (ouExponent x q)) (J x) V :=
    (((ou_exponent_smooth x).exp).ftaylorSeriesWithin hU.uniqueDiffOn).mono hVU
  have hsm : ContDiffOn ℝ ∞ (fun q => ∫ x,Real.exp (ouExponent x q) ∂μ) V := by
    apply smooth_mixture_criterion μ V Metric.isOpen_ball (fun q x => Real.exp (ouExponent x q)) J hJ
      (fun n q hq => (ou_kernel_jets_continuous n q (hVU hq)).aestronglyMeasurable) B
    intro n x q hq
    exact hbound n x q (hVK hq)
  exact (hsm.contDiffAt (Metric.ball_mem_nhds z (by linarith : 0<r/2))).contDiffWithinAt

/-- Every actual joint derivative can be brought inside the mixture integral. -/
theorem ou_gaussian_mixture_derivative {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (n : ℕ) (z : ℝ × (Fin d → ℝ)) (hz : 0<z.1) :
    iteratedFDerivWithin ℝ n (fun q : ℝ × (Fin d → ℝ) => ∫ x,Real.exp (ouExponent x q) ∂μ)
      {q | 0<q.1} z =
      ∫ x,iteratedFDerivWithin ℝ n (fun q => Real.exp (ouExponent x q)) {q | 0<q.1} z ∂μ := by
  let U : Set (ℝ × (Fin d → ℝ)) := {z | 0<z.1}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let K := Metric.closedBall z (r/2)
  let V := Metric.ball z (r/2)
  have hKU : K ⊆ U := (Metric.closedBall_subset_ball (by linarith : r/2<r)).trans hrU
  have hVK : V ⊆ K := Metric.ball_subset_closedBall
  have hVU : V ⊆ U := hVK.trans hKU
  have hb := fun n => ou_kernel_all_order_compact_bound K (isCompact_closedBall _ _) hKU n
  choose B hB hbound using hb
  let J := fun x : Fin d → ℝ => ftaylorSeriesWithin ℝ (fun q => Real.exp (ouExponent x q)) U
  have hJ x : HasFTaylorSeriesUpToOn ∞ (fun q => Real.exp (ouExponent x q)) (J x) V :=
    (((ou_exponent_smooth x).exp).ftaylorSeriesWithin hU.uniqueDiffOn).mono hVU
  have ht := smooth_mixture_taylor μ V Metric.isOpen_ball
    (fun q x => Real.exp (ouExponent x q)) J hJ
    (fun n q hq => (ou_kernel_jets_continuous n q (hVU hq)).aestronglyMeasurable) B
    (fun n x q hq => hbound n x q (hVK hq))
  have hzV : z∈V := Metric.mem_ball_self (by linarith : 0<r/2)
  have he := ht.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (m := n) (by exact_mod_cast le_top) Metric.isOpen_ball.uniqueDiffOn hzV
  rw [iteratedFDerivWithin_of_isOpen n Metric.isOpen_ball hzV] at he
  rw [iteratedFDerivWithin_of_isOpen n hU hz]
  exact he.symm
end Asakura.Chapter9
