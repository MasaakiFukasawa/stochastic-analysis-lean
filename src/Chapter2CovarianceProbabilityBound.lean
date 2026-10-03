import Chapter2LenglartConvergence
import Chapter2LocalizedApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The probability step of the Kunita-Watanabe estimate: the second
factor is a fixed finite random variable. Its large-value event is kept
explicit and then removed; no moment bound on that factor is assumed. -/
theorem covariance_probability_from_square_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C R : ℕ → Ω → ℝ) (B : Ω → ℝ) (hB : Measurable B)
    (hbound : ∀ n, ∀ᵐ ω ∂P, |C n ω| ≤ Real.sqrt (R n ω)*Real.sqrt (B ω))
    (hR : ∀ δ > 0, Tendsto (fun n => P {ω | δ ≤ R n ω}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ |C n ω|}) atTop (𝓝 0) := by
  apply probability_limit_of_arbitrary_remainder P _ (fun δ n => {ω | δ ≤ R n ω}) hR
  intro η hη
  have ht := finite_real_tail_probability P B hB
  have htr : Tendsto (fun k : ℕ => P.real {ω | (k:ℝ)+1 < B ω}) atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp ht
    simpa only [Measure.real,Function.comp_def,ENNReal.toReal_zero] using h
  obtain ⟨k,hk⟩ := (htr.eventually (gt_mem_nhds hη)).exists
  let K := (k:ℝ)+1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ := ε^2/K
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) hK
  refine ⟨δ,hδ,?_⟩
  intro n
  have hinc : {ω | ε ≤ |C n ω|} ≤ᵐ[P] {ω | δ ≤ R n ω} ∪ {ω | K < B ω} := by
    filter_upwards [hbound n] with ω hω
    intro he
    by_contra hh
    have hr : R n ω < δ := lt_of_not_ge (fun h => hh (Or.inl h))
    have hb : B ω ≤ K := le_of_not_gt (fun h => hh (Or.inr h))
    have hcs : ε ≤ Real.sqrt (R n ω)*Real.sqrt (B ω) := he.trans hω
    have hr0 : 0 ≤ R n ω := by
      by_contra hn
      rw [Real.sqrt_eq_zero_of_nonpos (not_le.1 hn).le,zero_mul] at hcs
      exact (not_le_of_gt hε) hcs
    have hb0 : 0 ≤ B ω := by
      by_contra hn
      rw [Real.sqrt_eq_zero_of_nonpos (not_le.1 hn).le,mul_zero] at hcs
      exact (not_le_of_gt hε) hcs
    have hs := pow_le_pow_left₀ hε.le hcs 2
    rw [mul_pow,Real.sq_sqrt hr0,Real.sq_sqrt hb0] at hs
    have hprod := mul_lt_mul_of_pos_right hr hK
    have heδ : δ*K = ε^2 := div_mul_cancel₀ _ hK.ne'
    rw [heδ] at hprod
    have hle := mul_le_mul_of_nonneg_left hb hr0
    linarith
  have h := (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hinc)).trans
    (measureReal_union_le (μ := P) {ω | δ ≤ R n ω} {ω | K < B ω})
  change P.real {ω | ε ≤ |C n ω|} ≤ P.real {ω | δ ≤ R n ω}+P.real {ω | K < B ω} at h
  exact h.trans (add_le_add le_rfl hk.le)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.covariance_probability_from_square_bound
