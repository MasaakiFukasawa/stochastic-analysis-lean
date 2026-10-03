import Chapter2WrittenGrid
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter2Written
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The DCT step for both event probabilities and weighted tail expectations. -/
theorem weighted_event_limit (E : ℕ → Set Ω) (A : Set Ω)
    (hE : ∀ n, MeasurableSet (E n)) (hA : MeasurableSet A)
    (hi : ∀ ω, Tendsto (fun n => (E n).indicator (fun _ => (1 : ℝ)) ω)
      atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) ω)))
    {Y : Ω → ℝ} (hmY : Measurable Y) (hY : Integrable Y P) :
    Tendsto (fun n => ∫ ω, (E n).indicator Y ω ∂P) atTop (𝓝 (∫ ω, A.indicator Y ω ∂P)) := by
  apply Asakura.manuscript_dominated_convergence P _ _ (fun ω => |Y ω|)
    (fun n => hmY.indicator (hE n)) (hmY.indicator hA) (continuous_abs.measurable.comp hmY) hY.abs
  · intro n
    exact Eventually.of_forall fun ω => by
      by_cases h : ω ∈ E n <;> simp [Set.indicator, h, Real.norm_eq_abs, abs_nonneg]
  · exact Eventually.of_forall fun ω => by
      simpa only [Set.indicator, ite_mul, one_mul, zero_mul] using (hi ω).mul_const (Y ω)

/-- Pass a weighted probability inequality through changing events. -/
theorem event_inequality_limit (E : ℕ → Set Ω) (A : Set Ω)
    (hE : ∀ n, MeasurableSet (E n)) (hA : MeasurableSet A)
    (hi : ∀ ω, Tendsto (fun n => (E n).indicator (fun _ => (1 : ℝ)) ω)
      atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) ω)))
    {Y : Ω → ℝ} (hmY : Measurable Y) (hY : Integrable Y P)
    (c : ℕ → ℝ) (a : ℝ) (hc : Tendsto c atTop (𝓝 a))
    (hineq : ∀ᶠ n in atTop, c n * P.real (E n) ≤ ∫ ω, (E n).indicator Y ω ∂P) :
    a * P.real A ≤ ∫ ω, A.indicator Y ω ∂P := by
  have hp := weighted_event_limit (P := P) E A hE hA hi
    (Y := fun _ : Ω => (1 : ℝ)) measurable_const (integrable_const (1 : ℝ))
  have heq (B : Set Ω) (hB : MeasurableSet B) :
      (∫ ω, B.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) = P.real B := by
    rw [integral_indicator hB]
    simp
  simp_rw [heq _ (hE _), heq _ hA] at hp
  exact le_of_tendsto_of_tendsto (hc.mul hp) (weighted_event_limit E A hE hA hi hmY hY) hineq

/-- A monotone limit requires strict levels when passing n→∞. -/
theorem strict_level_monotone_limit (u : ℕ → ℝ) (hu : Monotone u)
    {z b : ℝ} (ht : Tendsto u atTop (𝓝 z)) : (∃ n, b < u n) ↔ b < z := by
  constructor
  · rintro ⟨n, hn⟩
    exact hn.trans_le (hu.ge_of_tendsto ht n)
  · intro hb
    obtain ⟨n, hn⟩ := (ht.eventually (Ioi_mem_nhds hb)).exists
    exact ⟨n, hn⟩

/-- The final b↑a step of the corrected continuous-time Doob proof. -/
theorem doob_closed_threshold_from_strict {Z Y : Ω → ℝ}
    (hZ : Measurable Z) (hmY : Measurable Y) (hY : Integrable Y P)
    (hstrict : ∀ b : ℝ, 0 < b → b * P.real {ω | b < Z ω} ≤
      ∫ ω, {ω | b < Z ω}.indicator Y ω ∂P)
    {a : ℝ} (ha : 0 < a) :
    a * P.real {ω | a ≤ Z ω} ≤ ∫ ω, {ω | a ≤ Z ω}.indicator Y ω ∂P := by
  let b : ℕ → ℝ := fun n => a - 1/(n+1)
  have hb : Tendsto b atTop (𝓝 a) := by
    simpa [b] using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hba (n : ℕ) : b n < a := by
    have hp : (0 : ℝ) < 1 / (n+1) := by positivity
    dsimp [b]; linarith
  refine event_inequality_limit (fun n => {ω | b n < Z ω}) {ω | a ≤ Z ω}
    (fun n => measurableSet_lt measurable_const hZ) (measurableSet_le measurable_const hZ)
    ?_ hmY hY b a hb ?_
  · intro ω
    by_cases h : a ≤ Z ω
    · have hn (n : ℕ) : b n < Z ω := (hba n).trans_le h
      simpa [Set.indicator, h, hn] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    · have hz : Z ω < a := lt_of_not_ge h
      have he := hb.eventually (Ioi_mem_nhds hz)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      simp [Set.indicator, h, not_lt.mpr (le_of_lt hn)]
  · filter_upwards [hb.eventually (Ioi_mem_nhds ha)] with n hn
    exact hstrict _ hn

end Asakura.Chapter2Written
