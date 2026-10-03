import Chapter2CumulativeSeparation
import Chapter2StieltjesRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- For a measure supported on (a,b], the cumulative integral at an
arbitrary real time is its value at the time clamped into [a,b]. -/
theorem cumulative_integral_clamp
    (a b : ℝ) (hab : a ≤ b) (μ : Measure ℝ)
    (hsupp : ∀ᵐ r ∂μ, r ∈ Ioc a b) (g : ℝ → ℝ) (t : ℝ) :
    (∫ r in Iic t, g r ∂μ) = ∫ r in Iic (intervalClamp a b hab t), g r ∂μ := by
  apply setIntegral_congr_set
  filter_upwards [hsupp] with r hr
  change (r ≤ t) = (r ≤ intervalClamp a b hab t)
  apply propext
  by_cases hta : t ≤ a
  · have he : intervalClamp a b hab t = a := by
      exact congrArg Subtype.val (projIcc_of_le_left hab hta)
    rw [he]
    constructor <;> intro h <;> linarith [hr.1]
  · by_cases hbt : b ≤ t
    · have he : intervalClamp a b hab t = b := by
        exact congrArg Subtype.val (projIcc_of_right_le hab hbt)
      rw [he]
      exact iff_of_true (hr.2.trans hbt) hr.2
    · rw [intervalClamp_eq a b hab ⟨(not_le.1 hta).le,(not_le.1 hbt).le⟩]

/-- Vanishing cumulative integrals on the finite interval already
separate integrands for its Stieltjes measure. -/
theorem integrand_zero_of_interval_cumulative_zero
    (a b : ℝ) (hab : a ≤ b) (μ : Measure ℝ)
    (hsupp : ∀ᵐ r ∂μ, r ∈ Ioc a b) (g : ℝ → ℝ) (hg : Integrable g μ)
    (hz : ∀ t ∈ Icc a b, (∫ r in Iic t, g r ∂μ) = 0) : g =ᵐ[μ] 0 := by
  apply integrand_zero_of_cumulative_integrals_zero μ g hg
  intro t
  rw [cumulative_integral_clamp a b hab μ hsupp g t]
  exact hz _ (intervalClamp_mem a b hab t)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.cumulative_integral_clamp
#print axioms Asakura.Chapter2Complete.integrand_zero_of_interval_cumulative_zero
