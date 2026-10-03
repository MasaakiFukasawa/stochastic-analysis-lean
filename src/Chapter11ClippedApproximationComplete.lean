import Chapter2FiniteDensity
import Chapter2IntegralSquareContinuity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Remove clipping for a common elementary approximation. The measure
 may be a random finite Stieltjes measure and need not have an integrable mass. -/
theorem clipped_approximation_complete {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Ω → Measure ℝ)
    [∀ w,IsFiniteMeasure (μ w)] (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (J : ℕ → Ω × ℝ → ℝ) (hJ : ∀ n,Measurable (J n))
    (hJbound : ∀ n z,|J n z|≤(n:ℝ)+1) (p : ℝ) (hp : 0<p)
    (hi : ∀ᵐ w ∂P,Integrable (fun r => |H (w,r)|^p) (μ w))
    (hWm : ∀ n : ℕ,Measurable (fun w => ∫ r,|max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (H (w,r)))-H (w,r)|^p ∂μ w))
    (happrox : ∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,|J n (w,r)-max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (H (w,r)))|^p ∂μ w}) atTop (𝓝 0)) :
    (∀ n,∀ᵐ w ∂P,Integrable (fun r => |J n (w,r)-H (w,r)|^p) (μ w)) ∧
      ∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,|J n (w,r)-H (w,r)|^p ∂μ w}) atTop (𝓝 0) := by
  let k := fun n : ℕ => (n:ℝ)+1
  let Hm := fun n z => max (-(k n)) (min (k n) (H z))
  have hHm n : Measurable (Hm n) := measurable_const.max (measurable_const.min hH)
  have hHmb n z : |Hm n z| ≤ k n :=
    abs_le.2 ⟨le_max_left _ _,max_le (by dsimp [k]; linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩
  let R := fun n ω => ∫ r, |J n (ω,r)-H (ω,r)|^p ∂μ ω
  let U := fun n ω => ∫ r, |J n (ω,r)-Hm n (ω,r)|^p ∂μ ω
  let W := fun n ω => ∫ r, |Hm n (ω,r)-H (ω,r)|^p ∂μ ω
  have hWi n ω (hiω : Integrable (fun r => |H (ω,r)|^p) (μ ω)) : Integrable (fun r => |Hm n (ω,r)-H (ω,r)|^p) (μ ω) := by
    apply hiω.mono' ((((hHm n).sub hH).comp measurable_prodMk_left).norm.pow_const p).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro r
    change ‖|Hm n (ω,r)-H (ω,r)|^p‖ ≤ |H (ω,r)|^p
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    exact Real.rpow_le_rpow (abs_nonneg _) (truncation_error_bound (k n) _ (by dsimp [k]; positivity)) hp.le
  have hUi n ω : Integrable (fun r => |J n (ω,r)-Hm n (ω,r)|^p) (μ ω) := by
    apply Integrable.of_bound ((((hJ n).sub (hHm n)).comp measurable_prodMk_left).norm.pow_const p).aestronglyMeasurable ((2*k n)^p)
    apply Filter.Eventually.of_forall
    intro r
    change ‖|J n (ω,r)-Hm n (ω,r)|^p‖ ≤ (2*k n)^p
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
    have hj := hJbound n (ω,r)
    change |J n (ω,r)| ≤ k n at hj
    have ht := abs_sub_le (J n (ω,r)) 0 (Hm n (ω,r))
    simp only [sub_zero,zero_sub,abs_neg] at ht
    linarith [hHmb n (ω,r)]
  have hRi n : ∀ᵐ ω ∂P, Integrable (fun r => |J n (ω,r)-H (ω,r)|^p) (μ ω) := by
    filter_upwards [hi] with ω hiω
    apply (((hUi n ω).add (hWi n ω hiω)).const_mul ((2:ℝ)^p)).mono'
      ((((hJ n).sub hH).comp measurable_prodMk_left).norm.pow_const p).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro r
    change ‖|J n (ω,r)-H (ω,r)|^p‖ ≤
      (2:ℝ)^p*(|J n (ω,r)-Hm n (ω,r)|^p+|Hm n (ω,r)-H (ω,r)|^p)
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    exact power_error_triangle _ _ _ p hp.le
  have hbnd n : ∀ᵐ ω ∂P, R n ω ≤ (2:ℝ)^p*(U n ω+W n ω) := by
    filter_upwards [hi] with ω hiω
    have h := integral_mono_of_nonneg (μ := μ ω)
      (.of_forall (fun r => Real.rpow_nonneg (abs_nonneg (J n (ω,r)-H (ω,r))) p))
      (((hUi n ω).add (hWi n ω hiω)).const_mul ((2:ℝ)^p))
      (.of_forall (fun r => power_error_triangle (J n (ω,r)) (Hm n (ω,r)) (H (ω,r)) p hp.le))
    change (∫ r, |J n (ω,r)-H (ω,r)|^p ∂μ ω) ≤
      ∫ r, (2:ℝ)^p*(|J n (ω,r)-Hm n (ω,r)|^p+|Hm n (ω,r)-H (ω,r)|^p) ∂μ ω at h
    rw [integral_const_mul,integral_add (hUi n ω) (hWi n ω hiω)] at h
    exact h
  have hWlim : ∀ᵐ ω ∂P, Tendsto (fun n => W n ω) atTop (𝓝 0) := by
    filter_upwards [hi] with ω hiω
    have h := (truncation_power_integral_limit (μ ω) (fun r => H (ω,r))
      (hH.comp measurable_prodMk_left).aestronglyMeasurable p hp hiω).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using h
  refine ⟨hRi,?_⟩
  intro ε hε
  exact probability_error_sum_limit P R U W ((2:ℝ)^p) (Real.rpow_pos_of_pos (by norm_num) p) hbnd
    happrox (fun δ hδ => nonnegative_ae_limit_probability P W hWm
      (fun n ω => integral_nonneg (fun r => Real.rpow_nonneg (abs_nonneg _) p))
      hWlim δ hδ) ε hε

end Asakura.Chapter11
