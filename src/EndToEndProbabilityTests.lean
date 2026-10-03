import Chapter2BoundedProbabilityMean
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.EndToEnd
open Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The appendix's direct bounded-test argument, without an a.s. subsequence. -/
theorem probability_test_limit
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (Y : Ω → E)
    (hX : ∀ n,Measurable (X n)) (hY : Measurable Y)
    (hp : TendstoInMeasure P X atTop Y)
    (φ : E → ℝ) (hu : UniformContinuous φ)
    (K : ℝ) (hk : ∀ x,|φ x| ≤ K) :
    Tendsto (fun n => (∫ w,φ (X n w) ∂P)-(∫ w,φ (Y w) ∂P))
      atTop (𝓝 0) := by
  let C := 2*|K|+1
  have hC : 0 < C := by dsimp [C]; positivity
  let f := fun n w => φ (X n w)-φ (Y w)
  have hfm n : Measurable (f n) :=
    (hu.continuous.measurable.comp (hX n)).sub
      (hu.continuous.measurable.comp hY)
  have hfb n w : |f n w| ≤ C := by
    have h := norm_sub_le (φ (X n w)) (φ (Y w))
    simp only [Real.norm_eq_abs] at h
    have h1 := hk (X n w)
    have h2 := hk (Y w)
    dsimp [f,C]
    linarith [le_abs_self K]
  let R := fun n w => |f n w|/C
  have hRm n : Measurable (R n) := by
    simpa only [Real.norm_eq_abs] using (hfm n).norm.div_const C
  have hRb n w : 0 ≤ R n w ∧ R n w ≤ 1 :=
    ⟨div_nonneg (abs_nonneg _) hC.le,(div_le_one hC).mpr (hfb n w)⟩
  have hRp (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => P {w | ε ≤ R n w}) atTop (𝓝 0) := by
    obtain ⟨δ,hδ,hδφ⟩ := Metric.uniformContinuous_iff.mp hu (ε*C) (mul_pos hε hC)
    have hsub n : {w | ε ≤ R n w} ⊆ {w | δ ≤ dist (X n w) (Y w)} := by
      intro w hw
      by_contra hnot
      have hd : dist (X n w) (Y w) < δ := lt_of_not_ge hnot
      have hf := hδφ hd
      rw [Real.dist_eq] at hf
      have hw' : ε*C ≤ |f n w| := (le_div_iff₀ hC).mp hw
      exact (not_lt_of_ge hw') hf
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendstoInMeasure_iff_dist.mp hp δ hδ) (fun _ => bot_le) (fun n => measure_mono (hsub n))
  have hlim := bounded_error_mean_limit P R hRm hRb hRp
  have hfi n : Integrable (f n) P := Integrable.of_bound (hfm n).aestronglyMeasurable C
    (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hfb n w)
  have hnorm : Tendsto (fun n => ∫ w,|f n w| ∂P) atTop (𝓝 0) := by
    have hh := hlim.const_mul C
    simp only [mul_zero] at hh
    convert hh using 1
    funext n
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun w => (mul_div_cancel₀ _ hC.ne').symm
  have hzero : Tendsto (fun n => ∫ w,f n w ∂P) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hnorm
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f n)
  convert hzero using 1
  funext n
  have hi1 : Integrable (fun w => φ (X n w)) P :=
    Integrable.of_bound (hu.continuous.measurable.comp (hX n)).aestronglyMeasurable K
      (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hk (X n w))
  have hi2 : Integrable (fun w => φ (Y w)) P :=
    Integrable.of_bound (hu.continuous.measurable.comp hY).aestronglyMeasurable K
      (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hk (Y w))
  exact (integral_sub hi1 hi2).symm

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.probability_test_limit
