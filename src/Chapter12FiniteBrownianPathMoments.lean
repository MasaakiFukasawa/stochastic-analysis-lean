import Chapter12BrownianCompactPath
import Chapter12BrownianPathMoments

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def finiteBrownianCompactPath {Ω : Type*} {d : ℕ}
    (B : Fin d → ℝ≥0 → Ω → ℝ) (hc : ∀ i w,Continuous (fun t => B i t w))
    (T : ℝ) : Ω → C(Icc (0:ℝ) T,Fin d → ℝ) := fun w =>
  ⟨fun t i => B i ⟨t.val,t.property.1⟩ w,continuous_pi (fun i =>
    (hc i w).comp (continuous_subtype_val.subtype_mk (fun t : Icc (0:ℝ) T => t.property.1)))⟩

theorem finite_brownian_path_memLp {Ω : Type*} {d : ℕ} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : Fin d → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i,IsPreBrownianReal (B i) P) (hm : ∀ i t,Measurable (B i t))
    (hc : ∀ i w,Continuous (fun t => B i t w)) (T : ℝ≥0)
    (p : ℝ≥0∞) (hp : p≠⊤) : MemLp (finiteBrownianCompactPath B hc T) p P := by
  have hmi : ∀ i,Measurable (brownianCompactPath (B i) (hc i) T) := by
    intro i
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact hm i _
  have hi (i : Fin d) := brownian_path_memLp P (B i) (hB i) (hm i) (hc i) T
    (brownianCompactPath (B i) (hc i) T) (hmi i) (fun _ _ => rfl) p hp
  have hmv : Measurable (finiteBrownianCompactPath B hc T) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact Measurable.of_eval (fun i => hm i _)
  have hb : MemLp (fun w => ∑ i,‖brownianCompactPath (B i) (hc i) T w‖) p P :=
    memLp_finsetSum _ (fun i _ => (hi i).norm)
  apply hb.mono' hmv.aestronglyMeasurable
  filter_upwards [] with w
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro t
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro i
  exact ((brownianCompactPath (B i) (hc i) T w).norm_coe_le_norm t).trans
    (Finset.single_le_sum (fun j _ => norm_nonneg (brownianCompactPath (B j) (hc j) T w)) (Finset.mem_univ i))

end Asakura.Chapter12
