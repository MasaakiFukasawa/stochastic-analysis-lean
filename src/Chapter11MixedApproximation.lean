import Chapter11ClippedApproximationComplete

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.Chapter2Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The same clipped elementary approximants converge in L2 for the
 martingale clock and L1 for a dominated variation clock, locally in probability. -/
theorem mixed_clipped_approximation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ ν : Ω → Measure ℝ)
    [∀ w,IsFiniteMeasure (μ w)] [∀ w,IsFiniteMeasure (ν w)]
    (hν : ∀ w,ν w≤μ w) (hνm : Measurable (fun w => (ν w).real univ))
    (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (J : ℕ → Ω × ℝ → ℝ) (hJ : ∀ n,Measurable (J n))
    (hJb : ∀ n z,|J n z|≤(n:ℝ)+1)
    (happrox : ∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,(J n (w,r)-max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (H (w,r))))^2 ∂μ w}) atTop (𝓝 0)) :
    (∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,(J n (w,r)-max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (H (w,r))))^2 ∂ν w}) atTop (𝓝 0)) ∧
    (∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,|J n (w,r)-max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (H (w,r)))| ∂ν w}) atTop (𝓝 0)) := by
  let D := fun n z => J n z-max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (H z))
  have hDm n : Measurable (D n) := (hJ n).sub (measurable_const.max (measurable_const.min hH))
  have hDb n z : |D n z|≤2*((n:ℝ)+1) := by
    have hc : |max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (H z))|≤(n:ℝ)+1 :=
      abs_le.mpr ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α:=ℝ) n]) (min_le_left _ _)⟩
    exact (abs_sub _ _).trans (by linarith [hJb n z])
  have hi n w : Integrable (fun r => (D n (w,r))^2) (μ w) := by
    apply Integrable.of_bound (((hDm n).comp measurable_prodMk_left).pow_const 2).aestronglyMeasurable ((2*((n:ℝ)+1))^2)
    apply ae_of_all
    intro r
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq.mpr (by rw [abs_of_nonneg (by positivity : 0≤2*((n:ℝ)+1))];exact hDb n (w,r))
  have hsmall n w : (∫ r,(D n (w,r))^2 ∂ν w)≤∫ r,(D n (w,r))^2 ∂μ w :=
    integral_mono_measure (hν w) (ae_of_all _ fun r => sq_nonneg _) (hi n w)
  constructor
  · intro ε hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (happrox ε hε) (fun _ => bot_le)
    intro n
    exact measure_mono (fun w hw => hw.trans (hsmall n w))
  · intro ε hε
    have hcs n w : |∫ r,|D n (w,r)| ∂ν w|≤Real.sqrt (∫ r,(D n (w,r))^2 ∂μ w)*Real.sqrt ((ν w).real univ) := by
      have hm : MemLp (fun r => D n (w,r)) 2 (ν w) :=
        (memLp_two_iff_integrable_sq ((hDm n).comp measurable_prodMk_left).aestronglyMeasurable).mpr ((hi n w).mono_measure (hν w))
      have h := integral_product_square_bound (ν w) (fun r => |D n (w,r)|) (fun _ => 1) hm.norm (memLp_const 1)
      simp only [mul_one,sq_abs,one_pow,integral_const,smul_eq_mul,mul_one] at h
      exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hsmall n w)) (Real.sqrt_nonneg _))
    have hp := covariance_probability_from_square_bound P
      (fun n w => ∫ r,|D n (w,r)| ∂ν w) (fun n w => ∫ r,(D n (w,r))^2 ∂μ w)
      (fun w => (ν w).real univ) hνm (fun n => ae_of_all _ (hcs n)) happrox ε hε
    simpa only [abs_of_nonneg (integral_nonneg (fun r => abs_nonneg _))] using hp

end Asakura.Chapter11
