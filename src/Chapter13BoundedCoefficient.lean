import Chapter13MatrixNoiseConstruction
import Chapter13BoundedParameterEnergy

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Local pathwise bounds imply the local square-integrability needed by
the matrix Ito construction, without a uniform bound in the sample point. -/
theorem bounded_coefficient_square {Ω:Type*} [MeasurableSpace Ω]
    (S:Ω × ℝ → ℝ) (hm:Measurable S)
    (hb:∀w b,0≤b → ∃K:ℝ,0≤K ∧ ∀r∈Icc 0 b,|S (w,r)|≤K) :
    ∀w b,0≤b → IntervalIntegrable (fun r => S (w,r)^2) volume 0 b := by
  intro w b hb0
  obtain ⟨K,hK,hbound⟩:=hb w b hb0
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb0]
  apply (integrable_const (K^2)).mono' ((hm.comp (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hh:=pow_le_pow_left₀ (abs_nonneg (S (w,r))) (hbound r ⟨hr.1.le,hr.2⟩) 2
  simpa only [sq_abs,Function.comp_apply,id_eq] using hh

/-- Products of locally L2 real coefficients have integrable time paths. -/
theorem square_integrable_product (f g:ℝ → ℝ) (a b:ℝ)
    (hmf:Measurable f) (hmg:Measurable g)
    (hf:IntervalIntegrable (fun r => f r^2) volume a b)
    (hg:IntervalIntegrable (fun r => g r^2) volume a b) :
    IntervalIntegrable (fun r => f r*g r) volume a b := by
  apply (hf.add hg).mono_fun (hmf.mul hmg).aestronglyMeasurable
  apply ae_of_all
  intro r
  change ‖f r*g r‖≤‖f r^2+g r^2‖
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0≤f r^2+g r^2 from add_nonneg (sq_nonneg _) (sq_nonneg _))]
  have h:=sq_nonneg (|f r|-|g r|)
  rw [abs_mul]
  nlinarith [sq_abs (f r),sq_abs (g r)]
end Asakura.Chapter13
#print axioms Asakura.Chapter13.bounded_coefficient_square
#print axioms Asakura.Chapter13.square_integrable_product
