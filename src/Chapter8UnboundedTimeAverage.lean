import Chapter8SmoothCutoffApproximation
import Chapter8TimeAverageL1

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's cutoff argument: bounded Lipschitz time-average
convergence extends to the C1, integrable information entries. -/
theorem unbounded_stationary_time_average_L1 {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Measure E)
    (Y : Ω → ℝ → E) (hY : Measurable (Function.uncurry Y))
    (hcY : ∀ w,Continuous (Y w)) (hlaw : ∀ t,P.map (fun w => Y w t)=π)
    (T : ℕ → ℝ) (hT : ∀ n,0<T n)
    (hlim : ∀ (g : E → ℝ) (L : ℝ≥0),LipschitzWith L g →
      (∃ K : ℝ,0 ≤ K ∧ ∀ x,|g x| ≤ K) →
      Tendsto (fun n => ∫ w,|timeAverage (fun t => g (Y w t)) (T n)-(∫ x,g x ∂π)| ∂P)
        atTop (nhds 0))
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (hi : Integrable f π) :
    Tendsto (fun n => ∫ w,|timeAverage (fun t => f (Y w t)) (T n)-(∫ x,f x ∂π)| ∂P)
      atTop (nhds 0) := by
  let g := fun k x => informationCutoff (E := E) k x*f x
  have hgc k : Continuous (g k) := (informationCutoff (E := E) k).continuous.mul hf.continuous
  have hgi k : Integrable (g k) π := by
    apply hi.abs.mono' (hgc k).aestronglyMeasurable
    apply ae_of_all _
    intro x
    rw [Real.norm_eq_abs,show g k x=informationCutoff (E := E) k x*f x from rfl,abs_mul,
      abs_of_nonneg (informationCutoff (E := E) k).nonneg]
    exact mul_le_of_le_one_left (abs_nonneg _) (informationCutoff (E := E) k).le_one
  have hX n := (stationary_time_average_L1_bound P π Y hY hlaw f hf.continuous.measurable hi (T n) (hT n)).1
  have hgX k n := (stationary_time_average_L1_bound P π Y hY hlaw (g k) (hgc k).measurable (hgi k) (T n) (hT n)).1
  apply l1_limit_from_approximations P atTop
    (fun n w => timeAverage (fun t => f (Y w t)) (T n))
    (fun k n w => timeAverage (fun t => g k (Y w t)) (T n))
    (∫ x,f x ∂π) (fun k => ∫ x,g k x ∂π)
    (fun k => ∫ x,|f x-g k x| ∂π) hX hgX
    (smooth_cutoff_L1_approximation π f hf.continuous.measurable hi)
  · intro k
    rw [abs_sub_comm,← integral_sub hi (hgi k)]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x-g k x)
  · intro k n
    have hb := (stationary_time_average_L1_bound P π Y hY hlaw (fun x => f x-g k x)
      (hf.continuous.sub (hgc k)).measurable (hi.sub (hgi k)) (T n) (hT n)).2
    have he w : timeAverage (fun t => (f (Y w t)-g k (Y w t))) (T n)=
        timeAverage (fun t => f (Y w t)) (T n)-timeAverage (fun t => g k (Y w t)) (T n) := by
      simp only [timeAverage]
      rw [intervalIntegral.integral_sub (f := fun t => f (Y w t)) (g := fun t => g k (Y w t))
        ((hf.continuous.comp (hcY w)).intervalIntegrable _ _)
        (((hgc k).comp (hcY w)).intervalIntegrable _ _)]
      ring
    simpa only [he] using hb
  · intro k
    obtain ⟨⟨L,hL⟩,hb⟩ := smooth_cutoff_lipschitz f hf k
    exact hlim (g k) L hL hb

end Asakura.Chapter8
