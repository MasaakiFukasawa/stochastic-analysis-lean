import Chapter7RepeatedEvents
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Convert the conditional probability bound into the test-event inequality
used to iterate failures. -/
theorem conditional_failure_cut
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ m) (A : Set Ω) (hA : MeasurableSet[m] A)
    (q : ℝ) (hq : 0 ≤ q)
    (hc : ∀ᵐ w ∂P,P[(Aᶜ.indicator (fun _ => (1:ℝ)))|G] w ≤ q)
    (E : Set Ω) (hE : MeasurableSet[G] E) :
    P (E ∩ Aᶜ) ≤ ENNReal.ofReal q*P E := by
  have hEm : MeasurableSet[m] E := hG E hE
  have hi : Integrable (Aᶜ.indicator (fun _ : Ω => (1:ℝ))) P := (integrable_const _).indicator hA.compl
  have hh := integral_mono_ae (integrable_condExp.restrict (s := E)) (integrable_const (μ := P.restrict E) q)
    (ae_restrict_of_ae hc)
  rw [setIntegral_condExp hG hi hE] at hh
  rw [integral_indicator hA.compl,Measure.restrict_restrict hA.compl] at hh
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hh
  have hh' := ENNReal.ofReal_le_ofReal hh
  simpa only [mul_one,one_mul,ENNReal.ofReal_mul hq,ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (measure_ne_top _ _),
    inter_comm,mul_comm] using hh'

/-- The success-probability formulation used in the manuscript implies
infinitely many successful trials by the proved conditional iteration. -/
theorem conditional_success_infinitely_often
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ j,F j ≤ m)
    (A : ℕ → Set Ω) (hA : ∀ j,MeasurableSet[F (j+1)] (A j))
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hc : ∀ j,∀ᵐ w ∂P,p ≤ P[((A j).indicator (fun _ => (1:ℝ)))|F j] w) :
    ∀ᵐ w ∂P,∀ N : ℕ,∃ j,N ≤ j ∧ w ∈ A j := by
  apply repeated_events_infinitely_often P F hF A hA (ENNReal.ofReal (1-p))
    (by rw [ENNReal.ofReal_lt_one]; linarith)
  intro j E hE
  have hAm : MeasurableSet[m] (A j) := hle (j+1) _ (hA j)
  apply conditional_failure_cut P (F j) (hle j) (A j) hAm (1-p) (by linarith) _ E hE
  have he : (A j)ᶜ.indicator (fun _ : Ω => (1:ℝ)) =
      (fun _ => (1:ℝ))-(A j).indicator (fun _ => (1:ℝ)) := by
    funext w
    by_cases hw : w ∈ A j <;> simp [hw]
  have hh := condExp_sub (integrable_const (μ := P) (1:ℝ)) ((integrable_const (μ := P) (1:ℝ)).indicator hAm) (F j)
  filter_upwards [hh,hc j] with w hw hc
  rw [he,hw]
  simp only [Pi.sub_apply,condExp_const (hle j)]
  linarith

end Asakura.Chapter7
