import Chapter8StationaryIntegralL1
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- The actual smooth cutoffs used to truncate the information observable. -/
noncomputable def informationCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) : ContDiffBump (0:E) :=
  ⟨(n:ℝ)+1,2*((n:ℝ)+1),by positivity,by have := Nat.cast_nonneg (α := ℝ) n; linarith⟩

theorem smooth_cutoff_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (n : ℕ) :
    (∃ L,LipschitzWith L (fun x => informationCutoff (E := E) n x*f x)) ∧
    ∃ K : ℝ,0 ≤ K ∧ ∀ x,|informationCutoff (E := E) n x*f x| ≤ K := by
  have hc : ContDiff ℝ 1 (fun x => informationCutoff (E := E) n x*f x) := (informationCutoff (E := E) n).contDiff.mul hf
  have hs : HasCompactSupport (fun x => informationCutoff (E := E) n x*f x) :=
    (informationCutoff (E := E) n).hasCompactSupport.mul_right
  refine ⟨ContDiff.lipschitzWith_of_hasCompactSupport hs hc (by norm_num),?_⟩
  obtain ⟨K,hK⟩ := hs.exists_bound_of_continuous hc.continuous
  refine ⟨max K 0,le_max_right _ _,fun x => ?_⟩
  exact (show |informationCutoff (E := E) n x*f x| ≤ K from hK x).trans (le_max_left _ _)

/-- Dominated convergence removes the spatial cutoff using only L1
integrability of the original observable, uniformly in observation time. -/
theorem smooth_cutoff_L1_approximation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (π : Measure E) (f : E → ℝ) (hf : Measurable f) (hi : Integrable f π) :
    Tendsto (fun n => ∫ x,|f x-informationCutoff (E := E) n x*f x| ∂π) atTop (nhds 0) := by
  have hb n x : |f x-informationCutoff (E := E) n x*f x|  ≤  |f x| := by
    have hn : 0 ≤ informationCutoff (E := E) n x := (informationCutoff (E := E) n).nonneg
    have h1 : informationCutoff (E := E) n x ≤ 1 := (informationCutoff (E := E) n).le_one
    rw [show f x-informationCutoff (E := E) n x*f x=(1-informationCutoff (E := E) n x)*f x by ring,abs_mul,
      abs_of_nonneg (sub_nonneg.mpr h1)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
  have hm n : Measurable (fun x => |f x-informationCutoff (E := E) n x*f x|) := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply,Pi.mul_apply] using
      (hf.sub ((informationCutoff (E := E) n).continuous.measurable.mul hf)).norm
  have ht : Tendsto (fun n => ∫ x,|f x-informationCutoff (E := E) n x*f x| ∂π) atTop
      (nhds (∫ _ : E,(0:ℝ) ∂π)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (hm n).aestronglyMeasurable) hi.abs
    · intro n
      exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs,abs_abs] using hb n x)
    · apply ae_of_all _
      intro x
      obtain ⟨N,hN⟩ := exists_nat_ge ‖x‖
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have he : informationCutoff (E := E) n x=1 := (informationCutoff (E := E) n).one_of_mem_closedBall (by
        change dist x 0 ≤ (n:ℝ)+1
        rw [dist_zero_right]
        exact hN.trans ((Nat.cast_le.mpr hn).trans (by linarith)))
      simp [he]
  simpa only [integral_zero] using ht

end Asakura.Chapter8
