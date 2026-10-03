import Chapter2RandomIntegralMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 700000

/-- A uniform scalar bound suffices for the pth-power triangle estimate;
this also covers 0 < p < 1. -/
theorem power_error_triangle (x y z p : ℝ) (hp : 0 ≤ p) :
    |x-z|^p ≤ (2:ℝ)^p * (|x-y|^p+|y-z|^p) := by
  have ht := abs_sub_le x y z
  have hm : |x-z| ≤ 2*max |x-y| |y-z| := by
    linarith [le_max_left |x-y| |y-z|,le_max_right |x-y| |y-z|]
  calc
    _ ≤ (2*max |x-y| |y-z|)^p := Real.rpow_le_rpow (abs_nonneg _) hm hp
    _ = (2:ℝ)^p * (max |x-y| |y-z|)^p := Real.mul_rpow (by norm_num) (le_max_of_le_left (abs_nonneg _))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) p)
      rcases le_total |x-y| |y-z| with h|h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) p)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) p)

/-- Two probability-small errors give a probability-small total error. -/
theorem probability_error_sum_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R U V : ℕ → Ω → ℝ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ n, ∀ᵐ ω ∂P, R n ω ≤ C*(U n ω+V n ω))
    (hU : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ U n ω}) atTop (𝓝 0))
    (hV : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ V n ω}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ R n ω}) atTop (𝓝 0) := by
  have hδ : 0 < ε/(2*C) := div_pos hε (by positivity)
  have h := (hU _ hδ).add (hV _ hδ)
  simp only [zero_add] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
  intro n
  apply (measure_mono_ae (μ := P) (show {ω | ε ≤ R n ω} ≤ᵐ[P]
    {ω | ε/(2*C) ≤ U n ω} ∪ {ω | ε/(2*C) ≤ V n ω} from ?_)).trans (measure_union_le _ _)
  filter_upwards [hb n] with ω hbω
  intro hω
  by_contra hh
  have hu : U n ω < ε/(2*C) := lt_of_not_ge (fun h => hh (Or.inl h))
  have hv : V n ω < ε/(2*C) := lt_of_not_ge (fun h => hh (Or.inr h))
  have he : ε/(2*C)*(2*C) = ε := div_mul_cancel₀ _ (by positivity)
  have hu' := mul_lt_mul_of_pos_right hu (by positivity : 0 < 2*C)
  have hv' := mul_lt_mul_of_pos_right hv (by positivity : 0 < 2*C)
  change ε ≤ R n ω at hω
  nlinarith [hbω]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.power_error_triangle
#print axioms Asakura.Chapter2Complete.probability_error_sum_limit
