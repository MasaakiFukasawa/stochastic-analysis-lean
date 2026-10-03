import Chapter10KyleOrderMoment

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The equilibrium error variance gives integrable total absolute order
flow, despite the order-rate coefficient diverging at maturity. -/
theorem kyle_absolute_orders_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ℝ → Ω → ℝ)
    (hm : Measurable (Function.uncurry E)) (h2 : ∀ t,MemLp (E t) 2 P)
    (S0 T l : ℝ) (hS : 0≤S0) (hT : 0<T) (hl : 0<l)
    (hvar : ∀ t∈Ioo 0 T,(∫ w,(E t w)^2 ∂P)=S0*(T-t)/T) :
    Integrable (fun z : ℝ × Ω => E z.1 z.2/(l*(T-z.1))) ((volume.restrict (Ioo 0 T)).prod P) ∧
      ∀ᵐ w ∂P,Integrable (fun t => E t w/(l*(T-t))) (volume.restrict (Ioo 0 T)) := by
  let b := fun t => (Real.sqrt (S0/T)/l)*(T-t)^(-1/2:ℝ)
  have hb0 : IntegrableOn (fun t => (T-t)^(-1/2:ℝ)) (Ioc 0 T) volume := by
    simpa only [uIoc_of_le hT.le] using (terminal_inverse_sqrt_integrable T).1
  have hb : Integrable b (volume.restrict (Ioo 0 T)) :=
    (hb0.mono_set Ioo_subset_Ioc_self).const_mul _
  apply order_rate_integrable P (volume.restrict (Ioo 0 T))
    (fun t w => E t w/(l*(T-t))) b
    (hm.div (measurable_const.mul (measurable_const.sub measurable_fst))).aestronglyMeasurable
    (fun t => by simpa only [div_eq_mul_inv] using (h2 t).mul_const ((l*(T-t))⁻¹)) hb
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (kyle_order_second_moment P (E t) S0 T t l hS hT ht.2 hl (hvar t ht)).le

end Asakura.Chapter10
