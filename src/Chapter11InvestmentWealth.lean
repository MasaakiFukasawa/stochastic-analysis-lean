import Chapter11ExponentialSDE

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The precise wealth equation and exponential solution printed in the
investment section, for bounded progressively measurable ratios. -/
theorem investment_wealth_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hπm : Measurable π)
    (hπp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => π (z.1,z.2.val)))
    (K x r μ σ R : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K) (hx : 0<x) (hR : 0<R) :
    ∃ V N M : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F N ∧ LocalMProcessWitness P B.F M ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => σ*π z) N ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => V (realTimeClamp z.2) z.1*(σ*π z)) M ∧
      (∀ w t,0<V t w) ∧
      (∀ w t,t∈Icc 0 R → V (realTimeClamp t) w=
        x*Real.exp ((∫ s in 0..t,r+π (w,s)*(μ-r)-σ^2*(π (w,s))^2/2)+N (realTimeClamp t) w)) ∧
      (∀ t∈Icc 0 R,V (realTimeClamp t)=ᵐ[P]
        fun w => x+(∫ s in 0..t,V (realTimeClamp s) w*(r+π (w,s)*(μ-r)))+M (realTimeClamp t) w) := by
  let b := fun z : Ω × ℝ => r+π z*(μ-r)-σ^2*(π z)^2/2
  have hbm : Measurable b := (measurable_const.add (hπm.mul_const (μ-r))).sub (((hπm.pow_const 2).const_mul (σ^2)).div_const 2)
  have hbp d (hd : 0<d) : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => b (z.1,z.2.val)) :=
    (measurable_const.add ((hπp d hd).mul_const (μ-r))).sub ((((hπp d hd).pow_const 2).const_mul (σ^2)).div_const 2)
  have hbb z : |b z|≤|r|+K*|μ-r|+σ^2*K^2/2 := by
    have hs : (π z)^2≤K^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hK] using hb z)
    have hq : |σ^2*(π z)^2/2|≤σ^2*K^2/2 := by
      rw [abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) (by norm_num)
    have hp : |π z*(μ-r)| ≤ K*|μ-r| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb z) (abs_nonneg _)
    calc
      |b z| ≤ |r+π z*(μ-r)|+|σ^2*(π z)^2/2| := abs_sub _ _
      _ ≤ (|r|+|π z*(μ-r)|)+σ^2*K^2/2 := add_le_add (abs_add_le _ _) hq
      _ ≤ |r|+K*|μ-r|+σ^2*K^2/2 := by linarith
  obtain ⟨V,N,M,hN,hM,hNI,hMI,hpos,he,hsde,hVa,hVc⟩ := exponential_bounded_sde_constructed P B b (fun z => σ*π z)
    hbm (hπm.const_mul σ) hbp (fun d hd => (hπp d hd).const_mul σ)
    (|σ| *K) (|r|+K*|μ-r|+σ^2*K^2/2) (Real.log x) R (mul_nonneg (abs_nonneg _) hK)
    (fun z => by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg _)) hbb hR
  refine ⟨V,N,M,hN,hM,hNI,hMI,hpos,?_,?_⟩
  · intro w t ht
    rw [he w t ht,add_assoc,Real.exp_add,Real.exp_log hx]
  · intro t ht
    filter_upwards [hsde t ht] with w hw
    rw [Real.exp_log hx] at hw
    convert hw using 1
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only [b]
    ring

end Asakura.Chapter11
