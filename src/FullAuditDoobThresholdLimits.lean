import Chapter2WrittenThreshold
import FullAuditDoob

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter2Written

/-- The first c↓b passage in the printed continuous-time proof. -/
theorem weak_strict_from_closed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (M Y : Ω → ℝ)
    (hM : Measurable M) (hmY : Measurable Y) (hY : Integrable Y P)
    (hw : ∀ c > 0, c * P.real {ω | c ≤ M ω} ≤ ∫ ω, {ω | c ≤ M ω}.indicator Y ω ∂P)
    (b : ℝ) (hb : 0 < b) :
    b * P.real {ω | b < M ω} ≤ ∫ ω, {ω | b < M ω}.indicator Y ω ∂P := by
  let c := fun n : ℕ => b + 1/(n+1)
  have hc : Tendsto c atTop (𝓝 b) := by
    simpa [c] using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbc (n : ℕ) : b < c n := by
    dsimp [c]
    have h : (0 : ℝ) < 1/(n+1) := by positivity
    linarith
  refine event_inequality_limit (P := P) (fun n => {ω | c n ≤ M ω}) {ω | b < M ω}
    (fun n => measurableSet_le measurable_const hM) (measurableSet_lt measurable_const hM) ?_ hmY hY c b hc ?_
  · intro ω
    by_cases h : b < M ω
    · have he := hc.eventually (Iio_mem_nhds h)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      simp [Set.indicator,h,hn.le]
    · have hn (n : ℕ) : ¬ c n ≤ M ω := not_le.mpr ((le_of_not_gt h).trans_lt (hbc n))
      simp [Set.indicator,h,hn]
  · exact Eventually.of_forall fun n => hw (c n) (hb.trans (hbc n))

/-- The n→infinity step uses strict levels, allowing an infinite supremum. -/
theorem weak_strict_monotone_sup {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hM : ∀ n, Measurable (M n)) (hmono : ∀ ω, Monotone (fun n => M n ω))
    (hmY : Measurable Y) (hY : Integrable Y P)
    (hw : ∀ n b, 0 < b → b * P.real {ω | b < M n ω} ≤ ∫ ω, {ω | b < M n ω}.indicator Y ω ∂P)
    (b : ℝ) (hb : 0 < b) :
    b * P.real {ω | ENNReal.ofReal b < ⨆ n, ENNReal.ofReal (M n ω)} ≤
      ∫ ω, {ω | ENNReal.ofReal b < ⨆ n, ENNReal.ofReal (M n ω)}.indicator Y ω ∂P := by
  let A : Set Ω := {ω | ENNReal.ofReal b < ⨆ n, ENNReal.ofReal (M n ω)}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (Measurable.iSup fun n => (hM n).ennreal_ofReal)
  have he (ω : Ω) : ω ∈ A ↔ ∃ n, b < M n ω := by
    simp only [A,mem_setOf_eq,lt_iSup_iff]
    exact exists_congr fun n => ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb.le
  refine event_inequality_limit (P := P) (fun n => {ω | b < M n ω}) A
    (fun n => measurableSet_lt measurable_const (hM n)) hA ?_ hmY hY (fun _ => b) b tendsto_const_nhds ?_
  · intro ω
    by_cases h : ω ∈ A
    · obtain ⟨N,hN⟩ := (he ω).mp h
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hbn := hN.trans_le (hmono ω hn)
      simp [Set.indicator,h,hbn]
    · have hn (n : ℕ) : ¬ b < M n ω := fun hn => h ((he ω).mpr ⟨n,hn⟩)
      simp [Set.indicator,h,hn]
  · exact Eventually.of_forall fun n => hw n b hb

/-- The final b↑a passage for an extended nonnegative supremum. -/
theorem weak_closed_from_strict_ennreal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ≥0∞) (Y : Ω → ℝ)
    (hZ : Measurable Z) (hmY : Measurable Y) (hY : Integrable Y P)
    (hw : ∀ b > 0, b * P.real {ω | ENNReal.ofReal b < Z ω} ≤
      ∫ ω, {ω | ENNReal.ofReal b < Z ω}.indicator Y ω ∂P)
    (a : ℝ) (ha : 0 < a) :
    a * P.real {ω | ENNReal.ofReal a ≤ Z ω} ≤
      ∫ ω, {ω | ENNReal.ofReal a ≤ Z ω}.indicator Y ω ∂P := by
  let b := fun n : ℕ => a - 1/(n+1)
  have hb : Tendsto b atTop (𝓝 a) := by
    simpa [b] using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hba (n : ℕ) : b n < a := by
    dsimp [b]
    have h : (0 : ℝ) < 1/(n+1) := by positivity
    linarith
  refine event_inequality_limit (P := P) (fun n => {ω | ENNReal.ofReal (b n) < Z ω})
    {ω | ENNReal.ofReal a ≤ Z ω} (fun n => measurableSet_lt measurable_const hZ)
    (measurableSet_le measurable_const hZ) ?_ hmY hY b a hb ?_
  · intro ω
    by_cases h : ENNReal.ofReal a ≤ Z ω
    · have hn (n : ℕ) : ENNReal.ofReal (b n) < Z ω :=
        (ENNReal.ofReal_lt_ofReal_iff ha).mpr (hba n) |>.trans_le h
      simp [Set.indicator,h,hn]
    · have hz : Z ω < ENNReal.ofReal a := lt_of_not_ge h
      have he := (ENNReal.continuous_ofReal.tendsto a |>.comp hb).eventually (Ioi_mem_nhds hz)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      change Z ω < ENNReal.ofReal (b n) at hn
      simp [Set.indicator,h,not_lt.mpr hn.le]
  · filter_upwards [hb.eventually (Ioi_mem_nhds ha)] with n hn
    exact hw (b n) hn

end Asakura.FullAudit
