import Chapter2RandomCauchy
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecificLimits.Normed

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 700000

/-- Choose the rapid subsequence from the Cauchy condition, rather than
assuming its existence as an input to Borel-Cantelli. -/
theorem cauchy_choose_rapid_subsequence
    (r : ℕ → ℕ → ℝ)
    (hc : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, r n m < ε)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ n, r (k n) (k (n+1)) < ε n := by
  classical
  choose N hN using fun n => hc (ε n) (hε n)
  let k := fun n => n + (Finset.range (n+1)).sup N
  have hkn (n) : N n ≤ k n := by
    exact (Finset.le_sup (f := N) (Finset.mem_range.2 (Nat.lt_succ_self n))).trans (Nat.le_add_left _ _)
  have hk : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h := Finset.sup_mono (f := N) (Finset.range_mono (by omega : n+1 ≤ (n+1)+1))
    dsimp [k]
    omega
  exact ⟨k,hk,fun n => hN n (k n) (hkn n) (k (n+1)) ((hkn n).trans (hk.monotone (by omega)))⟩

/-- Markov's inequality for the bounded metric used to metrize
convergence in probability. -/
theorem truncated_distance_probability_bound
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    P {ω | ε < dist (X ω) (Y ω)} ≤
      ENNReal.ofReal ((∫ ω, min 1 (dist (X ω) (Y ω)) ∂P) / ε) := by
  let d := fun ω => min 1 (dist (X ω) (Y ω))
  have hd : Measurable d := measurable_const.min (hX.dist hY)
  have hd0 (ω) : 0 ≤ d ω := le_min zero_le_one dist_nonneg
  have hi : Integrable d P := Integrable.of_bound hd.aestronglyMeasurable 1 (.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hd0 ω)]
    exact min_le_left _ _)
  have hmark := meas_ge_le_lintegral_div (μ := P) hd.ennreal_ofReal.aemeasurable
    (ENNReal.ofReal_ne_zero_iff.2 hε) ENNReal.ofReal_ne_top
  have hinc : {ω | ε < dist (X ω) (Y ω)} ⊆ {ω | ENNReal.ofReal ε ≤ ENNReal.ofReal (d ω)} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (le_min hε1 hω.le)
  calc
    _ ≤ P {ω | ENNReal.ofReal ε ≤ ENNReal.ofReal (d ω)} := measure_mono hinc
    _ ≤ _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (.of_forall hd0),← ENNReal.ofReal_div_of_pos hε] at hmark
      exact hmark

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.cauchy_choose_rapid_subsequence
#print axioms Asakura.Chapter2Complete.truncated_distance_probability_bound
