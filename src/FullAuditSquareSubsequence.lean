import FullAuditTransportSeparation
import AppendixWrittenBorelCantelli
import Mathlib.Analysis.PSeries

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The printed Chebyshev estimate, followed by the appendix's counting-
 function proof of Borel-Cantelli, for the n-squared subsequence. -/
theorem square_rate_ae_convergence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ) (C : ℝ)
    (hm : ∀ n, Measurable (Z n)) (hi : ∀ n, Integrable (fun ω => (Z n ω)^2) P)
    (hbound : ∀ n, (∫ ω, (Z n ω)^2 ∂P) ≤ C/((n:ℝ)+1)^2) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (nhds 0) := by
  have hgood (ε : ℝ) (hε : 0 < ε) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |Z n ω| < ε := by
    let A := fun n => {ω | ε ≤ |Z n ω|}
    have hA : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le measurable_const (hm n).norm
    have hprob (n : ℕ) : P (A n) ≤ ENNReal.ofReal (C/ε^2/((n:ℝ)+1)^2) := by
      have h := (mul_meas_ge_le_integral_of_nonneg (ae_of_all P (fun ω => sq_nonneg (Z n ω))) (hi n) (ε^2)).trans (hbound n)
      have he : {ω | ε^2 ≤ (Z n ω)^2} = A n := by
        ext ω
        simp only [A,mem_setOf_eq]
        rw [← sq_abs (Z n ω),sq_le_sq₀ hε.le (abs_nonneg _)]
      rw [he] at h
      have hr : P.real (A n) ≤ C/ε^2/((n:ℝ)+1)^2 := by
        have hh : P.real (A n) ≤ (C/((n:ℝ)+1)^2)/ε^2 :=
          (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by simpa only [mul_comm] using h)
        convert hh using 1 <;> ring
      have ho := ENNReal.ofReal_le_ofReal hr
      rwa [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] at ho
    have hs : Summable (fun n : ℕ => C/ε^2/((n:ℝ)+1)^2) := by
      have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
      convert h.mul_left (C/ε^2) using 1
      funext n
      simp only [Nat.cast_add,Nat.cast_one]
      ring
    have hsum : ∑' n, P (A n) < ∞ := (ENNReal.tsum_le_tsum hprob).trans_lt hs.tsum_ofReal_lt_top
    filter_upwards [Asakura.written_borel_cantelli P A hA hsum] with ω hω
    obtain ⟨N,hN⟩ := hω.bddAbove
    filter_upwards [eventually_gt_atTop N] with n hn
    by_contra hh
    exact not_le_of_gt hn (hN (not_lt.mp hh))
  have hall := ae_all_iff.mpr (fun q : ℕ => hgood (1/((q:ℝ)+1)) (by positivity))
  filter_upwards [hall] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨q,hq⟩ := exists_nat_one_div_lt hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hω q)
  exact ⟨N,fun n hn => by simpa only [Real.dist_eq,sub_zero] using (hN n hn).trans hq⟩

end Asakura.FullAudit
