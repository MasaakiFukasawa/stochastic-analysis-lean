import Chapter11TimeMoments
import Chapter11BoundedStrategyIntegral

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The uniform real-moment estimate from the printed bounded strategy
hypothesis, with the stochastic integral and bracket constructed. -/
theorem bounded_strategy_all_moments {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hπ : Measurable π)
    (hπp : ∀ b,0<b → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => π (z.1,z.2.val)))
    (K x r μ σ T : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K) (hx : 0<x) :
    ∃ N C : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F N ∧ ItoCovarianceFormula P B.F (B.W 0) (fun z => σ*π z) N ∧
      LocalCovarianceWitness P B.F N N C ∧
      (∀ t,0≤t → C (realTimeClamp t)=ᵐ[P] fun w => ∫ s in 0..t,(σ*π (w,s))^2) ∧
      ∀ q t,t∈Icc 0 T →
        let V := fun w => x*Real.exp ((∫ s in 0..t,r+π (w,s)*(μ-r))+N (realTimeClamp t) w-C (realTimeClamp t) w/2)
        Integrable (fun w => (V w)^q) P ∧
        (∫ w,(V w)^q ∂P)≤x^q*Real.exp (|q| *((|r|+K*|μ-r|)*T)+|q^2-q| *((|σ| *K)^2*T)/2) := by
  obtain ⟨N,C,hN,hNI,hC,hCe,hCb,_,_⟩ := bounded_strategy_integral P B
    (fun z => σ*π z) (hπ.const_mul σ) (fun b h => (hπp b h).const_mul σ)
    (|σ| *K) (mul_nonneg (abs_nonneg _) hK) (fun z => by
      rw [abs_mul];exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg _))
  refine ⟨N,C,hN,hNI,hC,hCe,?_⟩
  intro q t ht
  have hAm : Measurable (fun w => ∫ s in 0..t,r+π (w,s)*(μ-r)) := by
    simp only [intervalIntegral.integral_of_le ht.1]
    exact ((measurable_const.add (hπ.mul_const (μ-r))).stronglyMeasurable.integral_prod_right').measurable
  exact exponential_wealth_real_moment P (by simp) B.F B.mono B.le B.null N C hN hC
    (realTimeClamp t) (real_time_below t ht.1 (EReal.coe_lt_top t))
    (fun w => ∫ s in 0..t,r+π (w,s)*(μ-r)) hAm ((|r|+K*|μ-r|)*T) ((|σ| *K)^2*T) x q hx
    (ae_of_all _ (bounded_strategy_drift π K r μ T t hK hb ht))
    ((hCb t ht.1).mono (fun w hw => ⟨hw.1,hw.2.trans (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg _))⟩))

end Asakura.Chapter11
