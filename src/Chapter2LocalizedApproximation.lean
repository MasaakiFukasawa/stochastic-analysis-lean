import Chapter2PathMetricSubsequence
import Chapter2TruncationLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 900000

/-- A stopped error estimate controls the original error except on the
explicit event where the localization stops too early. -/
theorem localized_error_probability_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R S : Ω → ℝ) (E : Set Ω) (hS : Integrable S P)
    (hpos : ∀ᵐ ω ∂P, 0 ≤ S ω) (hRS : ∀ ω ∉ E, R ω ≤ S ω)
    (ε : ℝ) (hε : 0 < ε) :
    P {ω | ε ≤ R ω} ≤ P E + ENNReal.ofReal ((∫ ω, S ω ∂P)/ε) := by
  have hmark := meas_ge_le_lintegral_div (μ := P) hS.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_ne_zero_iff.2 hε) ENNReal.ofReal_ne_top
  have hinc : {ω | ε ≤ R ω} ⊆ E ∪ {ω | ENNReal.ofReal ε ≤ ENNReal.ofReal (S ω)} := by
    intro ω hω
    by_cases he : ω ∈ E
    · exact Or.inl he
    · exact Or.inr (ENNReal.ofReal_le_ofReal (hω.trans (hRS ω he)))
  have h := (measure_mono (μ := P) hinc).trans (measure_union_le _ _)
  apply h.trans
  rw [← ofReal_integral_eq_lintegral_ofReal hS hpos,
    ← ENNReal.ofReal_div_of_pos hε] at hmark
  exact add_le_add le_rfl hmark

/-- This is the probability-convergence step after choosing the stopped
Lp approximants. It retains the exceptional-event term explicitly. -/
theorem localized_error_probability_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R S : ℕ → Ω → ℝ) (E : ℕ → Set Ω)
    (hS : ∀ n, Integrable (S n) P) (hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ S n ω)
    (hRS : ∀ n ω, ω ∉ E n → R n ω ≤ S n ω)
    (hE : Tendsto (fun n => P (E n)) atTop (𝓝 0))
    (hmean : Tendsto (fun n => ∫ ω, S n ω ∂P) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ R n ω}) atTop (𝓝 0) := by
  have hm : Tendsto (fun n => ENNReal.ofReal ((∫ ω, S n ω ∂P)/ε)) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hmean.div_const ε)
    simp only [zero_div,ENNReal.ofReal_zero] at h
    convert h using 1
    funext n
    rfl
  have hu := hE.add hm
  simp only [zero_add] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ => bot_le) (fun n => localized_error_probability_bound P (R n) (S n) (E n)
      (hS n) (hpos n) (hRS n) ε hε)

/-- Increasing cofinal localizing times make premature stopping events
have probability tending to zero. -/
theorem cofinal_stopping_probability_limit
    {Ω α : Type*} [MeasurableSpace Ω] [LinearOrder α]
    (P : Measure Ω) [IsFiniteMeasure P] (τ : ℕ → Ω → α) (t : α)
    (hm : ∀ n, MeasurableSet {ω | τ n ω < t})
    (hmono : ∀ ω, Monotone (fun n => τ n ω))
    (hcofinal : ∀ ω, ∃ n, t ≤ τ n ω) :
    Tendsto (fun n => P {ω | τ n ω < t}) atTop (𝓝 0) := by
  have hanti : Antitone (fun n => {ω | τ n ω < t}) := by
    intro n k hnk ω hω
    exact (hmono ω hnk).trans_lt hω
  have he : (⋂ n, {ω | τ n ω < t}) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro ω hω
    obtain ⟨n,hn⟩ := hcofinal ω
    exact (not_lt_of_ge hn) (Set.mem_iInter.1 hω n)
  have h := tendsto_measure_iInter_atTop (fun n => (hm n).nullMeasurableSet) hanti
    (show ∃ n, P {ω | τ n ω < t} ≠ ∞ from ⟨0,measure_ne_top _ _⟩)
  simp only [he,measure_empty] at h
  convert h using 1
  funext n
  rfl

/-- A finite real random variable exceeds the integer cutoffs with
probability tending to zero. -/
theorem finite_real_tail_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) :
    Tendsto (fun n : ℕ => P {ω | (n:ℝ)+1 < Z ω}) atTop (𝓝 0) := by
  have hm (n : ℕ) : MeasurableSet {ω | (n:ℝ)+1 < Z ω} := measurableSet_lt measurable_const hZ
  have hanti : Antitone (fun n : ℕ => {ω | (n:ℝ)+1 < Z ω}) := by
    intro n k hnk ω hω
    have hnk' : (n:ℝ) ≤ k := by exact_mod_cast hnk
    change (k:ℝ)+1 < Z ω at hω
    change (n:ℝ)+1 < Z ω
    linarith
  have he : (⋂ n : ℕ, {ω | (n:ℝ)+1 < Z ω}) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro ω hω
    obtain ⟨n,hn⟩ := exists_nat_ge (Z ω)
    have h := Set.mem_iInter.1 hω n
    change (n:ℝ)+1 < Z ω at h
    linarith
  have h := tendsto_measure_iInter_atTop (fun n => (hm n).nullMeasurableSet) hanti
    (show ∃ n : ℕ, P {ω | (n:ℝ)+1 < Z ω} ≠ ∞ from ⟨0,measure_ne_top _ _⟩)
  rw [he,measure_empty] at h
  convert h using 1
  funext n
  rfl

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.localized_error_probability_bound
#print axioms Asakura.Chapter2Complete.localized_error_probability_limit
#print axioms Asakura.Chapter2Complete.cofinal_stopping_probability_limit

#print axioms Asakura.Chapter2Complete.finite_real_tail_probability
