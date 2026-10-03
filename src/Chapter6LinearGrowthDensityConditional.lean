import Chapter6LinearGrowthItoConditional
import Chapter6LinearGrowthEnergyConditional

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem linear_growth_density_conditional_lower_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H N : Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ j t,Measurable[B.F t] (H j t)) (hHc : ∀ j w,Continuous (fun t => H j t w))
    (hN : ∀ j,LocalMProcessWitness P B.F (N j))
    (hNI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (fun z => H j (realTimeClamp z.2) z.1) (N j))
    (R : ℝ) (hR : 0<R) (b : ℝ → (Fin d → ℝ) → (Fin d → ℝ))
    (hb : ∀ r,Measurable (b r)) (K : ℝ) (hK : 0≤K)
    (hbb : ∀ r x,‖WithLp.toLp 2 (b r x)‖≤K*(1+‖WithLp.toLp 2 x‖))
    (hrep : ∀ j w r,r∈Icc 0 R → H j (realTimeClamp r) w=b r (fun i => B.W i (realTimeClamp r) w) j)
    (A : Ω → ℝ) (hAm : Measurable A)
    (hAe : A=ᵐ[P] fun w => ∫ r in 0..R,∑ j,(H j (realTimeClamp r) w)^2)
    (hDi : Integrable (fun w => Real.exp ((∑ j,N j (realTimeClamp R) w)-A w/2)) P) :
    let V := fun w i => B.W i (realTimeClamp R) w
    ∀ᵐ w ∂P,Real.exp (-(2*Real.sqrt R*((2*K^2*(3+2*(d:ℝ)*R)+(2/R+2*(d:ℝ)))/2)+R*(2*K^2*(3+2*(d:ℝ)*R))/2)*(1+‖WithLp.toLp 2 (V w)‖^2))
      ≤P[(fun w => Real.exp ((∑ j,N j (realTimeClamp R) w)-A w/2))|MeasurableSpace.comap V inferInstance] w := by
  let V := fun w i => B.W i (realTimeClamp R) w
  let Z := fun w => ∑ j,N j (realTimeClamp R) w
  obtain ⟨hZi,hZb⟩ := linear_growth_ito_conditional_bound P B H N hHa hHc hN hNI R hR b hb K hK hbb hrep
  obtain ⟨hEi,hEb⟩ := linear_growth_energy_conditional_bound P B H hHa hHc R hR b hb K hK hbb hrep
  have hAi : Integrable A P := hEi.congr hAe.symm
  have hAc : ∀ᵐ w ∂P,P[A|MeasurableSpace.comap V inferInstance] w≤R*(2*K^2*(3+2*(d:ℝ)*R))*(1+‖WithLp.toLp 2 (V w)‖^2) := by
    filter_upwards [condExp_congr_ae (m := MeasurableSpace.comap V inferInstance) hAe,hEb] with w he hb
    rw [he]
    exact le_of_abs_le hb
  have hVm : Measurable V := measurable_pi_iff.mpr (fun i =>
    ((B.martingale i).adapted P B.F _ (changed_time_finite R hR.le)).mono (B.le _) le_rfl)
  have hl := exponential_conditional_lower_bound P (MeasurableSpace.comap V inferInstance) hVm.comap_le
    Z A (fun w => 2*Real.sqrt R*((2*K^2*(3+2*(d:ℝ)*R)+(2/R+2*(d:ℝ)))/2)*(1+‖WithLp.toLp 2 (V w)‖^2))
    (fun w => R*(2*K^2*(3+2*(d:ℝ)*R))*(1+‖WithLp.toLp 2 (V w)‖^2)) hZi hAi
    (by simpa only [Z,div_eq_mul_inv,mul_comm,one_mul] using hDi)
    (hZb.mono (fun w hw => neg_le_of_abs_le hw)) hAc
  filter_upwards [hl] with w hw
  convert hw using 1
  · congr 1
    ring
  · simp only [Z,V,div_eq_mul_inv,mul_comm,one_mul]

end Asakura.Chapter6
