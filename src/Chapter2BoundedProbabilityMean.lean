import Chapter2RandomIntegralMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- The elementary expectation bound converting probability convergence
of bounded errors into convergence for the manuscript's expectation metric. -/
theorem bounded_error_mean_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hm : Measurable R) (hb : ∀ ω, 0 ≤ R ω ∧ R ω ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (∫ ω, R ω ∂P) ≤ δ+P.real {ω | δ ≤ R ω} := by
  classical
  let E := {ω | δ ≤ R ω}
  have hE : MeasurableSet E := measurableSet_le measurable_const hm
  have hRi : Integrable R P := Integrable.of_bound hm.aestronglyMeasurable 1
    (.of_forall (fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hb ω).1]; exact (hb ω).2))
  have hEi : Integrable (E.indicator (fun _ : Ω => (1:ℝ))) P :=
    (integrable_const (1:ℝ)).indicator hE
  have h := integral_mono hRi ((integrable_const δ).add hEi) (fun ω => by
    change R ω ≤ δ+E.indicator (fun _ : Ω => (1:ℝ)) ω
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      linarith [(hb ω).2]
    · rw [indicator_of_notMem hω]
      exact (not_le.1 hω).le.trans (by simp))
  change (∫ ω, R ω ∂P) ≤ ∫ ω, δ+E.indicator (fun _ : Ω => (1:ℝ)) ω ∂P at h
  rw [integral_add (integrable_const δ) hEi,integral_indicator hE] at h
  simpa only [integral_const,smul_eq_mul,Measure.real,measure_univ,ENNReal.toReal_one,one_mul,
    Measure.restrict_apply MeasurableSet.univ,univ_inter,mul_one] using h

/-- For measurable errors between 0 and 1, probability convergence to
zero implies expectation convergence to zero. -/
theorem bounded_error_mean_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (R n))
    (hb : ∀ n ω, 0 ≤ R n ω ∧ R n ω ≤ 1)
    (hl : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ R n ω}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, R n ω ∂P) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact .of_forall (fun n => ha.trans_le (integral_nonneg (fun ω => (hb n ω).1)))
  · intro ε hε
    have hδ : 0 < ε/2 := half_pos hε
    have hp : Tendsto (fun n => P.real {ω | ε/2 ≤ R n ω}) atTop (𝓝 0) := by
      have h := (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp (hl _ hδ)
      simpa only [Measure.real,Function.comp_def,ENNReal.toReal_zero] using h
    filter_upwards [hp.eventually (gt_mem_nhds hδ)] with n hn
    have h := bounded_error_mean_bound P (R n) (hm n) (hb n) (ε/2) hδ.le
    linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.bounded_error_mean_bound
#print axioms Asakura.Chapter2Complete.bounded_error_mean_limit
