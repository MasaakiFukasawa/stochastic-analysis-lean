import Chapter11WealthMoments
import Chapter11BoundedStrategyIntegral

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Real moments for the printed exponential with ordinary drift integral,
for any actual integral of the bounded progressive volatility. -/
theorem bounded_exponential_real_moments {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b H : Ω × ℝ → ℝ) (hbm : Measurable b) (hHm : Measurable H)
    (hHp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (K L x R : ℝ) (hK : 0≤K) (hL : 0≤L)
    (hHb : ∀ z,|H z|≤K) (hbb : ∀ z,|b z|≤L)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) H N)
    (q t : ℝ) (ht : t∈Icc 0 R) :
    let V := fun w => Real.exp (x+(∫ s in 0..t,b (w,s))+N (realTimeClamp t) w)
    Integrable (fun w => (V w)^q) P ∧
      (∫ w,(V w)^q ∂P)≤(Real.exp x)^q*Real.exp (|q| *(L*R+K^2*R/2)+|q^2-q| *(K^2*R)/2) := by
  obtain ⟨Z,C,hZ,hZI,hC,_,hCb,_,_⟩ := bounded_strategy_integral P B H hHm hHp K hK hHb
  have hNZ := hNI.unique P (by simp) B.F B.mono B.le B.null (B.W 0) N Z H (B.martingale 0) hN hZ hZI
  have hCm : Measurable (C (realTimeClamp t)) :=
    ((covariance_adapted_variation P B.F B.mono B.le hZ hZ hC).adapted _
      (real_time_below t ht.1 (EReal.coe_lt_top t))).mono (B.le _) le_rfl
  let A := fun w => (∫ s in 0..t,b (w,s))+C (realTimeClamp t) w/2
  have hAm : Measurable A := by
    dsimp only [A]
    apply Measurable.add _ (hCm.div_const 2)
    simp only [intervalIntegral.integral_of_le ht.1]
    exact (hbm.stronglyMeasurable.integral_prod_right').measurable
  have hc : ∀ᵐ w ∂P,0≤C (realTimeClamp t) w ∧ C (realTimeClamp t) w≤K^2*R :=
    (hCb t ht.1).mono (fun w hw => ⟨hw.1,hw.2.trans (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg _))⟩)
  have ha : ∀ᵐ w ∂P,|A w|≤L*R+K^2*R/2 := by
    filter_upwards [hc] with w hw
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=t)
      (fun s _ => show ‖b (w,s)‖≤L by simpa only [Real.norm_eq_abs] using hbb (w,s))
    simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] at hi
    have hh : |∫ s in 0..t,b (w,s)|≤L*R := hi.trans (mul_le_mul_of_nonneg_left ht.2 hL)
    dsimp only [A]
    calc
      _ ≤ |∫ s in 0..t,b (w,s)|+|C (realTimeClamp t) w/2| := abs_add_le _ _
      _ ≤ L*R+K^2*R/2 := by
        rw [abs_of_nonneg (div_nonneg hw.1 (by norm_num))]
        exact add_le_add hh (div_le_div_of_nonneg_right hw.2 (by norm_num))
  have hv := exponential_wealth_real_moment P (by simp) B.F B.mono B.le B.null Z C hZ hC
    (realTimeClamp t) (real_time_below t ht.1 (EReal.coe_lt_top t)) A hAm
    (L*R+K^2*R/2) (K^2*R) (Real.exp x) q (Real.exp_pos _) ha hc
  have he : (fun w => (Real.exp (x+(∫ s in 0..t,b (w,s))+N (realTimeClamp t) w))^q)=ᵐ[P]
      fun w => (Real.exp x*Real.exp (A w+Z (realTimeClamp t) w-C (realTimeClamp t) w/2))^q := by
    filter_upwards [hNZ] with w hw
    rw [hw _ (real_time_below t ht.1 (EReal.coe_lt_top t)),←Real.exp_add]
    congr 2
    dsimp only [A]
    ring
  exact ⟨hv.1.congr he.symm,by rw [integral_congr_ae he];exact hv.2⟩

end Asakura.Chapter11
