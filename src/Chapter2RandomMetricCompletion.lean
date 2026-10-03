import Chapter2RapidSubsequence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The rapid subsequence and its almost-sure limit, derived from the
Cauchy condition for the expectation of the truncated distance. -/
theorem truncated_metric_cauchy_subsequence
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X : ℕ → Ω → E) (hm : ∀ n, Measurable (X n))
    (hc : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      (∫ ω, min 1 (dist (X n ω) (X m ω)) ∂P) < ε) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ ω ∂P, ∃ y, Tendsto (fun n => X (k n) ω) atTop (𝓝 y) := by
  obtain ⟨k,hk,hsmall⟩ := cauchy_choose_rapid_subsequence
    (fun n m => ∫ ω, min 1 (dist (X n ω) (X m ω)) ∂P) hc
    (fun n => (1/4:ℝ)^n) (fun n => pow_pos (by norm_num) n)
  refine ⟨k,hk,?_⟩
  let d := fun n => (1/2:ℝ)^n
  have hd : Summable d := summable_geometric_of_abs_lt_one (by norm_num)
  have hb (n) : P {ω | d n < dist (X (k n) ω) (X (k (n+1)) ω)} ≤ ENNReal.ofReal (d n) := by
    have hp : 0 < d n := pow_pos (by norm_num) n
    have h1 : d n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    apply (truncated_distance_probability_bound P (X (k n)) (X (k (n+1))) (hm _) (hm _) (d n) hp h1).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_of_nonneg_right (hsmall n).le hp.le).trans_eq
    change (1/4:ℝ)^n / (1/2:ℝ)^n = (1/2:ℝ)^n
    rw [← div_pow]
    norm_num
  have hs : (∑' n, P {ω | d n < dist (X (k n) ω) (X (k (n+1)) ω)}) < ∞ := by
    apply (ENNReal.tsum_le_tsum hb).trans_lt
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (pow_pos (by norm_num : (0:ℝ)<1/2) n).le) hd]
    exact ENNReal.ofReal_lt_top
  exact random_summable_increment_limit P (fun n => X (k n)) d hd
    (fun n => measurableSet_lt measurable_const ((hm _).dist (hm _))) hs

/-- The exceptional set where the chosen subsequence does not converge
is measurable; setting all terms to a fixed value there gives a measurable
limit and convergence on every sample path. -/
theorem measurable_limit_after_null_modification
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (e : E) (X : ℕ → Ω → E) (hm : ∀ n, Measurable (X n))
    (hlim : ∀ᵐ ω ∂P, ∃ y, Tendsto (fun n => X n ω) atTop (𝓝 y)) :
    ∃ (N : Set Ω) (Y : Ω → E), MeasurableSet N ∧ P N = 0 ∧ Measurable Y ∧
      (∀ ω, Tendsto (fun n => if ω ∈ N then e else X n ω) atTop (𝓝 (Y ω))) := by
  classical
  let C := {ω | ∃ y, Tendsto (fun n => X n ω) atTop (𝓝 y)}
  have hCm : MeasurableSet C := measurableSet_exists_tendsto hm
  let Y := fun ω => if h : ω ∈ C then h.choose else e
  have hconv (ω) : Tendsto (fun n => if ω ∈ Cᶜ then e else X n ω) atTop (𝓝 (Y ω)) := by
    by_cases h : ω ∈ C
    · simpa [Y,h] using h.choose_spec
    · simpa [Y,h] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => e) atTop (𝓝 e))
  have hYm : Measurable Y := measurable_of_tendsto_metrizable
    (fun n => Measurable.ite hCm.compl measurable_const (hm n)) (tendsto_pi_nhds.2 hconv)
  refine ⟨Cᶜ,Y,hCm.compl,?_,hYm,?_⟩
  · change P {ω | ¬ ∃ y, Tendsto (fun n => X n ω) atTop (𝓝 y)} = 0
    exact ae_iff.1 hlim
  · intro ω
    by_cases h : ω ∈ Cᶜ
    · simpa only [if_pos h] using hconv ω
    · simpa only [if_neg h] using hconv ω

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.truncated_metric_cauchy_subsequence
#print axioms Asakura.Chapter2Complete.measurable_limit_after_null_modification
