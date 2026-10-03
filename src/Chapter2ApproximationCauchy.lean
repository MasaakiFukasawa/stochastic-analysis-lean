import Chapter2ProbabilityErrorSum

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

theorem probability_error_sum_limit_eventually
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R U V : ℕ → Ω → ℝ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, R n ω ≤ C*(U n ω+V n ω))
    (hU : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ U n ω}) atTop (𝓝 0))
    (hV : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ V n ω}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ R n ω}) atTop (𝓝 0) := by
  have hδ : 0 < ε/(2*C) := div_pos hε (by positivity)
  have h := (hU _ hδ).add (hV _ hδ)
  simp only [zero_add] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h (.of_forall (fun _ => bot_le))
  filter_upwards [hb] with n hbn
  apply (measure_mono_ae (μ := P) (show {ω | ε ≤ R n ω} ≤ᵐ[P]
    {ω | ε/(2*C) ≤ U n ω} ∪ {ω | ε/(2*C) ≤ V n ω} from ?_)).trans (measure_union_le _ _)
  filter_upwards [hbn] with ω hbω
  intro hω
  by_contra hh
  have hu : U n ω < ε/(2*C) := lt_of_not_ge (fun h => hh (Or.inl h))
  have hv : V n ω < ε/(2*C) := lt_of_not_ge (fun h => hh (Or.inr h))
  have he : ε/(2*C)*(2*C) = ε := div_mul_cancel₀ _ (by positivity)
  have hu' := mul_lt_mul_of_pos_right hu (by positivity : 0 < 2*C)
  have hv' := mul_lt_mul_of_pos_right hv (by positivity : 0 < 2*C)
  change ε ≤ R n ω at hω
  nlinarith [hbω]

/-- Local square-integral approximation is Cauchy along any two tail
subsequences. Integrability is needed only eventually on this fixed horizon. -/
theorem square_error_tail_difference_limit
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (μ : Ω → Measure S) (J : ℕ → Ω → S → ℝ) (H : Ω → S → ℝ)
    (hi : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, Integrable (fun r => (J n ω r-H ω r)^2) (μ ω))
    (hl : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ∫ r, (J n ω r-H ω r)^2 ∂μ ω}) atTop (𝓝 0))
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ ∫ r, (J (a n) ω r-J (b n) ω r)^2 ∂μ ω}) atTop (𝓝 0) := by
  apply probability_error_sum_limit_eventually P _
    (fun n ω => ∫ r, (J (a n) ω r-H ω r)^2 ∂μ ω)
    (fun n ω => ∫ r, (J (b n) ω r-H ω r)^2 ∂μ ω) 2 (by norm_num) _
    (fun δ hδ => (hl δ hδ).comp ha) (fun δ hδ => (hl δ hδ).comp hb) ε hε
  filter_upwards [ha.eventually hi,hb.eventually hi] with n hia hib
  filter_upwards [hia,hib] with ω hiaω hibω
  have h := integral_mono_of_nonneg (μ := μ ω)
    (.of_forall (fun r => sq_nonneg (J (a n) ω r-J (b n) ω r)))
    ((hiaω.add hibω).const_mul 2) (.of_forall (fun r => by
      change (J (a n) ω r-J (b n) ω r)^2 ≤ 2*((J (a n) ω r-H ω r)^2+(J (b n) ω r-H ω r)^2)
      nlinarith [sq_nonneg (J (a n) ω r+J (b n) ω r-2*H ω r)]))
  change (∫ r, (J (a n) ω r-J (b n) ω r)^2 ∂μ ω) ≤
    ∫ r, 2*((J (a n) ω r-H ω r)^2+(J (b n) ω r-H ω r)^2) ∂μ ω at h
  rw [integral_const_mul,integral_add hiaω hibω] at h
  exact h

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.probability_error_sum_limit_eventually
#print axioms Asakura.Chapter2Complete.square_error_tail_difference_limit
