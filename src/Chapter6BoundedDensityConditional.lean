import Chapter6BoundedItoConditionalBound
import Chapter6EuclideanEnergyBound

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem bounded_density_conditional_lower_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H N : Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ j t,Measurable[B.F t] (H j t)) (hHc : ∀ j w,Continuous (fun t => H j t w))
    (hN : ∀ j,LocalMProcessWitness P B.F (N j))
    (hNI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (fun z => H j (realTimeClamp z.2) z.1) (N j))
    (R : ℝ) (hR : 0<R) (b : ℝ → (Fin d → ℝ) → (Fin d → ℝ))
    (hb : ∀ r,Measurable (b r)) (K : ℝ) (hK : 0≤K)
    (hbb : ∀ r x,‖WithLp.toLp 2 (b r x)‖≤K)
    (hrep : ∀ j w r,r∈Icc 0 R → H j (realTimeClamp r) w=b r (fun i => B.W i (realTimeClamp r) w) j)
    (A : Ω → ℝ) (hAm : Measurable A)
    (hAe : A=ᵐ[P] fun w => ∫ r in 0..R,∑ j,(H j (realTimeClamp r) w)^2)
    (hDi : Integrable (fun w => Real.exp ((∑ j,N j (realTimeClamp R) w)-A w/2)) P) :
    let V := fun w i => B.W i (realTimeClamp R) w
    ∀ᵐ w ∂P,Real.exp (-K*(‖WithLp.toLp 2 (V w)‖+2*Real.sqrt ((d:ℝ)*R))-K^2*R/2)
      ≤P[(fun w => Real.exp ((∑ j,N j (realTimeClamp R) w)-A w/2))|MeasurableSpace.comap V inferInstance] w := by
  let V := fun w i => B.W i (realTimeClamp R) w
  let Z := fun w => ∑ j,N j (realTimeClamp R) w
  obtain ⟨hZi,hZb⟩ := bounded_ito_conditional_bound P B H N hHa hHc hN hNI R hR b hb K hK hbb hrep
  have hAb : ∀ᵐ w ∂P,0≤A w ∧ A w≤K^2*R := by
    filter_upwards [hAe] with w hw
    rw [hw]
    refine euclidean_time_energy_bound _ R hR.le ?_ K hK ?_
    · exact (continuous_pi (fun j => (hHc j w).comp real_time_clamp_continuous)).continuousOn
    · intro r hr
      have he : (fun j => H j (realTimeClamp r) w)=b r (fun i => B.W i (realTimeClamp r) w) := funext (fun j => hrep j w r hr)
      rw [he]
      exact hbb _ _
  have hAi : Integrable A P := Integrable.of_bound hAm.aestronglyMeasurable (K^2*R)
    (hAb.mono (fun w hw => by simpa only [Real.norm_eq_abs,abs_of_nonneg hw.1] using hw.2))
  have hAc := condExp_le_nonneg_const (μ := P) (m := MeasurableSpace.comap V inferInstance)
    (show 0≤K^2*R by positivity) (hAb.mono (fun _ h => h.2))
  have hVm : Measurable V := measurable_pi_iff.mpr (fun i =>
    ((B.martingale i).adapted P B.F _ (changed_time_finite R hR.le)).mono (B.le _) le_rfl)
  have hl := exponential_conditional_lower_bound P (MeasurableSpace.comap V inferInstance) hVm.comap_le
    Z A (fun w => K*(‖WithLp.toLp 2 (V w)‖+2*Real.sqrt ((d:ℝ)*R))) (fun _ => K^2*R) hZi hAi
    (by simpa only [Z,div_eq_mul_inv,mul_comm,one_mul] using hDi)
    (hZb.mono (fun w hw => neg_le_of_abs_le hw)) hAc
  simpa only [Z,V,neg_mul,div_eq_mul_inv,mul_comm,one_mul] using hl

end Asakura.Chapter6
