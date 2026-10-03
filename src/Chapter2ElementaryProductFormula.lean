import Chapter2SignedDifferenceIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false

/-- The Stieltjes integral for the two trading jumps is evaluated against
an actual finite signed measure. The purchase at time zero is excluded. -/
theorem elementary_trading_cost (X : ℝ → ℝ) (G a b t : ℝ) :
    signedIntegralRaw ((Measure.dirac a).toSignedMeasure-(Measure.dirac b).toSignedMeasure)
      ((Ioc 0 t).indicator (fun r => G*X r)) =
      (if 0 < a ∧ a ≤ t then G*X a else 0)-(if 0 < b ∧ b ≤ t then G*X b else 0) := by
  rw [signed_difference_integral]
  · simp only [integral_dirac,indicator_apply,mem_Ioc]
  · exact (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))

/-- The atomic trading measure has exactly the Stieltjes increments
of the right-continuous holding strategy. -/
theorem elementary_trading_measure_increments (G a b s t : ℝ)
    (hab : a < b) (hst : s ≤ t) :
    G*((Measure.dirac a).toSignedMeasure-(Measure.dirac b).toSignedMeasure) (Ioc s t) =
      (Ico a b).indicator (fun _ => G) t-(Ico a b).indicator (fun _ => G) s := by
  rw [VectorMeasure.sub_apply,Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
    Measure.toSignedMeasure_apply_measurable measurableSet_Ioc]
  simp only [Measure.real,Measure.dirac_apply' _ measurableSet_Ioc,indicator_apply,mem_Ioc,mem_Ico]
  by_cases hsa : s < a <;> by_cases hta : t < a <;>
    by_cases hsb : s < b <;> by_cases htb : t < b <;>
    simp [← not_lt,hsa,hta,hsb,htb] <;> grind

/-- The product-minus-cash formula in the motivation is exactly the
stopped-price increment used to construct the elementary Ito integral.
Initial purchases and all endpoint cases are included. -/
theorem elementary_product_minus_cost (X : ℝ → ℝ) (G a b t : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (ht : 0 ≤ t) :
    (Ico a b).indicator (fun _ => G) t * X t -
      (Ico a b).indicator (fun _ => G) 0 * X 0 -
      signedIntegralRaw ((Measure.dirac a).toSignedMeasure-(Measure.dirac b).toSignedMeasure)
        ((Ioc 0 t).indicator (fun r => G*X r)) =
      G*(X (min b t)-X (min a t)) := by
  rw [elementary_trading_cost]
  by_cases hat : a ≤ t
  · by_cases hbt : b ≤ t
    · rw [min_eq_left hbt,min_eq_left hat]
      by_cases ha0 : a = 0
      · subst a
        simp [indicator_apply,not_lt_of_ge hbt,hab,ht,hbt]
        ring
      · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        simp [indicator_apply,not_lt_of_ge hbt,not_le_of_gt hap,hap,hat,hbt,ha.trans_lt hab]
        ring
    · have htb : t < b := lt_of_not_ge hbt
      rw [min_eq_right htb.le,min_eq_left hat]
      by_cases ha0 : a = 0
      · subst a
        simp [indicator_apply,ht,htb,hab,hbt]
        ring
      · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        simp [indicator_apply,hat,htb,not_le_of_gt hap,hap,hbt]
        ring
  · have hta : t < a := lt_of_not_ge hat
    rw [min_eq_right (hta.trans hab).le,min_eq_right hta.le]
    have hap : 0 < a := ht.trans_lt hta
    simp [indicator_apply,hat,not_le_of_gt hap,not_le_of_gt (hta.trans hab)]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.elementary_product_minus_cost
