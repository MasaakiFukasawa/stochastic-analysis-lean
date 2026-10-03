import FullAuditChapter4Gronwall

open MeasureTheory Set
namespace Asakura.FullAudit

/-- A deterministic drift concentrated at one instant vanishes in every time integral. -/
theorem hjm_null_time_drift (s : ℝ) :
    (fun t : ℝ => if t=1 ∧ 1 ≤ s then (1:ℝ) else 0) =ᵐ[volume] 0 := by
  filter_upwards [volume.ae_ne (1:ℝ)] with t ht
  simp [ht]

theorem hjm_null_time_integral (a b s : ℝ) :
    (∫ t in a..b, if t=1 ∧ 1 ≤ s then (1:ℝ) else 0) = 0 := by
  calc
    _ = ∫ t in a..b, (0:ℝ) := intervalIntegral.integral_congr_ae ((hjm_null_time_drift s).mono (fun _ h _ => h))
    _ = 0 := by simp

/-- At t=1,s=2 the same drift is nonzero, while sigma=0 forces HJM's RHS to zero. -/
theorem hjm_pointwise_counterexample :
    (if (1:ℝ)=1 ∧ 1 ≤ (2:ℝ) then (1:ℝ) else 0) ≠ 0*0 := by norm_num

/-- The printed summation duplicates Gamma^j instead of summing all intervals. -/
theorem cheyette_wrong_index :
    (1:ℝ)*(1+2) ≠ 1*(2+2) := by norm_num

/-- Positive deterministic rates distinguish the accrued bond from its discount factor. -/
theorem caplet_wrong_bond :
    max ((2:ℝ)-1) 0 ≠ max ((1/2:ℝ)-1) 0 := by norm_num

/-- Zero volatility cannot be normalized to quadratic variation density one. -/
theorem zero_volatility_not_unit : ((0:ℝ)/|0|)^2 ≠ 1 := by norm_num

/-- The actual forward payoff identity, with delta>0. -/
theorem caplet_payoff_identity (p K δ : ℝ) (hδ : 0 < δ) :
    δ * max ((p-1)/δ-K) 0 = max (p-(1+δ*K)) 0 := by
  rw [mul_max_of_nonneg _ _ (le_of_lt hδ)]
  congr 1
  · field_simp
    <;> ring
  · ring

end Asakura.FullAudit
