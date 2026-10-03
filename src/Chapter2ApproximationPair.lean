import Chapter2ApproximationCauchy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

theorem square_error_two_approximations_limit
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (μ : Ω → Measure S) (J K : ℕ → Ω → S → ℝ) (H : Ω → S → ℝ)
    (hi : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, Integrable (fun r => (J n ω r-H ω r)^2) (μ ω))
    (hl : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ∫ r, (J n ω r-H ω r)^2 ∂μ ω}) atTop (𝓝 0))
    (hki : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, Integrable (fun r => (K n ω r-H ω r)^2) (μ ω))
    (hkl : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ∫ r, (K n ω r-H ω r)^2 ∂μ ω}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ ∫ r, (J n ω r-K n ω r)^2 ∂μ ω}) atTop (𝓝 0) := by
  apply probability_error_sum_limit_eventually P _
    (fun n ω => ∫ r, (J n ω r-H ω r)^2 ∂μ ω)
    (fun n ω => ∫ r, (K n ω r-H ω r)^2 ∂μ ω) 2 (by norm_num) _
    hl hkl ε hε
  filter_upwards [hi,hki] with n hia hib
  filter_upwards [hia,hib] with ω hiaω hibω
  have h := integral_mono_of_nonneg (μ := μ ω)
    (.of_forall (fun r => sq_nonneg (J n ω r-K n ω r)))
    ((hiaω.add hibω).const_mul 2) (.of_forall (fun r => by
      change (J n ω r-K n ω r)^2 ≤ 2*((J n ω r-H ω r)^2+(K n ω r-H ω r)^2)
      nlinarith [sq_nonneg (J n ω r+K n ω r-2*H ω r)]))
  change (∫ r, (J n ω r-K n ω r)^2 ∂μ ω) ≤
    ∫ r, 2*((J n ω r-H ω r)^2+(K n ω r-H ω r)^2) ∂μ ω at h
  rw [integral_const_mul,integral_add hiaω hibω] at h
  exact h


end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.square_error_two_approximations_limit
