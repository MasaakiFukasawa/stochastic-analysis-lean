import FullAuditTimeAveragePaths

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem time_average_abs_le (f : ℝ → ℝ) (K t : ℝ) (ht : 0 < t)
    (hb : ∀ u, |f u| ≤ K) : |timeAverage f t| ≤ K := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := (0:ℝ)) (b := t)
    (fun u _ => by simpa only [Real.norm_eq_abs] using hb u)
  rw [Real.norm_eq_abs,sub_zero,abs_of_pos ht] at h
  rw [timeAverage,abs_mul,abs_of_pos (inv_pos.mpr ht)]
  have he := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ht.le)
  convert he using 1 <;> field_simp

theorem time_average_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ → ℝ) (hX : Measurable (Function.uncurry X)) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (fun ω => timeAverage (X ω) t) := by
  simp only [timeAverage,intervalIntegral.integral_of_le ht]
  exact (hX.stronglyMeasurable.integral_prod_right.measurable).const_mul _

/-- The second half of the printed time-average proof. The variance bound
 from its first half is the explicit input; the entire square-subsequence,
 appendix Borel-Cantelli, and intervening-time argument is checked here. -/
theorem bounded_time_average_ae_from_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ → ℝ)
    (hX : Measurable (Function.uncurry X)) (hc : ∀ ω, Continuous (X ω))
    (K C l : ℝ) (hK : 0 ≤ K) (hb : ∀ ω u, |X ω u| ≤ K)
    (hvar : ∀ t > 0, (∫ ω, (timeAverage (X ω) t-l)^2 ∂P) ≤ C/t) :
    ∀ᵐ ω ∂P, Tendsto (timeAverage (X ω)) atTop (nhds l) := by
  let Z : ℕ → Ω → ℝ := fun n ω => timeAverage (X ω) (((n:ℝ)+1)^2)-l
  have hm : ∀ n, Measurable (Z n) := fun n =>
    (time_average_measurable X hX _ (sq_nonneg _)).sub measurable_const
  have hi : ∀ n, Integrable (fun ω => (Z n ω)^2) P := by
    intro n
    have hlp : MemLp (Z n) 2 P := MemLp.of_bound (hm n).aestronglyMeasurable (K+|l|) (by
      apply ae_of_all _
      intro ω
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add (time_average_abs_le (X ω) K (((n:ℝ)+1)^2) (by positivity) (hb ω)) le_rfl))
    exact (memLp_two_iff_integrable_sq hlp.aestronglyMeasurable).mp hlp
  have hseq := square_rate_ae_convergence P Z C hm hi (fun n => hvar _ (by positivity))
  filter_upwards [hseq] with ω hω
  have h1 : Tendsto (fun n : ℕ => timeAverage (X ω) (((n:ℝ)+1)^2)) atTop (nhds l) := by
    have h := hω.add_const l
    simpa only [Z,sub_add_cancel,zero_add] using h
  have h2 : Tendsto (fun n : ℕ => timeAverage (X ω) ((n:ℝ)^2)) atTop (nhds l) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Nat.cast_add,Nat.cast_one] using h1
  exact time_average_square_extension (X ω) (hc ω) K l hK (hb ω) h2

end Asakura.FullAudit
