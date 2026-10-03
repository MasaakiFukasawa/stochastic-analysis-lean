import Chapter2BoundedProbabilityMean
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The written bounded-uniformly-continuous test argument for the joint law.
The first coordinate may vary with n and may depend on the clock. -/
theorem joint_clock_test_limit
    {Ω E H : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MetricSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Ω → E) (A : ℕ → Ω → H) (c : H)
    (hB : ∀ n,Measurable (B n)) (hA : ∀ n,Measurable (A n))
    (hp : TendstoInMeasure P A atTop (fun _ => c))
    (φ : E × H → ℝ) (hu : UniformContinuous φ)
    (K : ℝ) (hk : ∀ x,|φ x| ≤ K) :
    Tendsto (fun n => (∫ w,φ (B n w,A n w) ∂P)-(∫ w,φ (B n w,c) ∂P))
      atTop (𝓝 0) := by
  let C := 2*|K|+1
  have hC : 0 < C := by dsimp [C]; positivity
  let f := fun n w => φ (B n w,A n w)-φ (B n w,c)
  have hfm n : Measurable (f n) :=
    (hu.continuous.measurable.comp ((hB n).prodMk (hA n))).sub
      (hu.continuous.measurable.comp ((hB n).prodMk measurable_const))
  have hfb n w : |f n w| ≤ C := by
    have h := norm_sub_le (φ (B n w,A n w)) (φ (B n w,c))
    simp only [Real.norm_eq_abs] at h
    have h1 := hk (B n w,A n w)
    have h2 := hk (B n w,c)
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
    have hsub n : {w | ε ≤ R n w} ⊆ {w | δ ≤ dist (A n w) c} := by
      intro w hw
      by_contra hnot
      have hd : dist (B n w,A n w) (B n w,c) < δ := by
        simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using lt_of_not_ge hnot
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
  have hi1 : Integrable (fun w => φ (B n w,A n w)) P :=
    Integrable.of_bound (hu.continuous.measurable.comp ((hB n).prodMk (hA n))).aestronglyMeasurable K
      (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hk (B n w,A n w))
  have hi2 : Integrable (fun w => φ (B n w,c)) P :=
    Integrable.of_bound (hu.continuous.measurable.comp ((hB n).prodMk measurable_const)).aestronglyMeasurable K
      (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hk (B n w,c))
  exact (integral_sub hi1 hi2).symm

end Asakura.Chapter7
