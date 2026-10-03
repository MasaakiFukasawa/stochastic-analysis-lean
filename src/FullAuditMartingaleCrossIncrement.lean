import FullAuditContinuousOptional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- The integrability needed for every product in the printed square-increment
 calculation follows from L2, including the unbounded case. -/
theorem l2_product_increment_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {U V : Ω → ℝ} (hU : MemLp U 2 P) (hV : MemLp V 2 P) :
    Integrable (U * (V-U)) P := by
  exact hU.integrable_mul (hV.sub hU)

/-- The centered increment and pull-out calculation at the earlier time. -/
theorem martingale_cross_increment_zero {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t)) (h2 : ∀ t, MemLp (X t) 2 P)
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (a b : ι) (hab : a ≤ b) : P[X a * (X b-X a) | F a] =ᵐ[P] 0 := by
  have hdiff := condExp_sub ((h2 b).integrable (by norm_num)) ((h2 a).integrable (by norm_num)) (F a)
  have hself : P[X a | F a] = X a := condExp_of_stronglyMeasurable (hle a) (hm a).stronglyMeasurable
    ((h2 a).integrable (by norm_num))
  have hz : P[X b-X a | F a] =ᵐ[P] 0 := by
    filter_upwards [hdiff,hmart a b hab] with ω hd hm
    simp only [Pi.sub_apply,hself,hm,sub_self,Pi.zero_apply] at hd ⊢
    exact hd
  have hp := condExp_mul_of_stronglyMeasurable_left (hm a).stronglyMeasurable
    (l2_product_increment_integrable P (h2 a) (h2 b))
    (((h2 b).integrable (by norm_num)).sub ((h2 a).integrable (by norm_num)))
  filter_upwards [hp,hz] with ω hp hz
  simpa only [Pi.mul_apply,hz,Pi.zero_apply,mul_zero] using hp

noncomputable def crossIncrement {Ω ι : Type*} [LinearOrder ι]
    (X : ι → Ω → ℝ) (a b t : ι) : Ω → ℝ :=
  X (min t a) * (X (min t b)-X (min t a))

/-- The three positions of s relative to [a,b] in the manuscript. This proves
 the martingale property of the cross term underlying the square-increment sum. -/
theorem cross_increment_martingale {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t)) (h2 : ∀ t, MemLp (X t) 2 P)
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (a b : ι) (hab : a ≤ b) (s t : ι) (hst : s ≤ t) :
    P[crossIncrement X a b t | F s] =ᵐ[P] crossIncrement X a b s := by
  by_cases hbs : b ≤ s
  · have hat := hab.trans (hbs.trans hst)
    have hbt := hbs.trans hst
    simp only [crossIncrement,min_eq_right hat,min_eq_right hbt,min_eq_right (hab.trans hbs),min_eq_right hbs]
    exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable (hle s)
      (((hm a).mono (hF (hab.trans hbs)) le_rfl).mul
        (((hm b).mono (hF hbs) le_rfl).sub ((hm a).mono (hF (hab.trans hbs)) le_rfl))).stronglyMeasurable
      (l2_product_increment_integrable P (h2 a) (h2 b)))
  · have hsb : s ≤ b := le_of_not_ge hbs
    by_cases has : a ≤ s
    · have hat := has.trans hst
      simp only [crossIncrement,min_eq_right hat,min_eq_right has,min_eq_left hsb]
      have hsm : s ≤ min t b := le_min hst hsb
      have hself : P[X a | F s] = X a := condExp_of_stronglyMeasurable (hle s)
        ((hm a).mono (hF has) le_rfl).stronglyMeasurable ((h2 a).integrable (by norm_num))
      have hd := condExp_sub ((h2 (min t b)).integrable (by norm_num)) ((h2 a).integrable (by norm_num)) (F s)
      have hp := condExp_mul_of_stronglyMeasurable_left
        ((hm a).mono (hF has) le_rfl).stronglyMeasurable
        (l2_product_increment_integrable P (h2 a) (h2 (min t b)))
        (((h2 (min t b)).integrable (by norm_num)).sub ((h2 a).integrable (by norm_num)))
      filter_upwards [hp,hd,hmart s (min t b) hsm] with ω hp hd hmart
      simp only [Pi.mul_apply,Pi.sub_apply] at hp hd ⊢
      rw [hp,hd,hmart,hself]
    · have hsa : s ≤ a := le_of_not_ge has
      have hsm : s ≤ min t a := le_min hst hsa
      have hmin : min t a ≤ min t b := min_le_min_left t hab
      have hz := martingale_cross_increment_zero P F hle X hm h2 hmart (min t a) (min t b) hmin
      have hc := condExp_congr_ae (m := F s) hz
      have htower := condExp_condExp_of_le (hF hsm) (hle (min t a))
        (μ := P) (f := crossIncrement X a b t)
      have he := htower.symm.trans hc
      simpa only [crossIncrement,min_eq_left hsa,min_eq_left hsb,sub_self,mul_zero,condExp_zero] using he

end Asakura.FullAudit
