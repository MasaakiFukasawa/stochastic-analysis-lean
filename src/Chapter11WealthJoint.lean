import Chapter11StrategyMoments
import Chapter5TimePrimitiveL2

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Joint measurability of the local martingale on real, finite times;
the artificial open endpoint of the process encoding is never evaluated. -/
theorem half_local_joint_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : HalfClosedTime → MeasurableSpace Ω)
    (hle : ∀ t,F t≤m) (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P F N) :
    Measurable (fun z : Ω × ℝ => N (realTimeClamp z.2) z.1) := by
  have ht (r : ℝ) : realTimeClamp (T:=(⊤:EReal)) r<⊤ :=
    (real_time_clamp_mono (le_max_left r 0)).trans_lt
      (real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _))
  have hc w : Continuous (fun r : ℝ => N (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hN.path P F w _ (ht r)).comp real_time_clamp_continuous.continuousAt
  exact (measurable_uncurry_of_continuous_of_measurable hc
    (fun r => (hN.adapted P F _ (ht r)).mono (hle _) le_rfl)).comp measurable_swap

/-- The real-power process of exponential wealth is integrable in time and
probability. In particular q=2(1-gamma) is justified for every gamma. -/
theorem exponential_wealth_time_moments {Ω : Type*} [m : MeasurableSpace Ω]
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
      let V := fun z : Ω × ℝ => x*Real.exp ((∫ s in 0..z.2,r+π (z.1,s)*(μ-r))+N (realTimeClamp z.2) z.1-C (realTimeClamp z.2) z.1/2)
      Measurable V ∧ (∀ z,0<V z) ∧
      ∀ q : ℝ,Integrable (fun z => (V z)^q) (P.prod (volume.restrict (Icc 0 T))) := by
  obtain ⟨N,C,hN,hNI,hC,hCe,hmom⟩ := bounded_strategy_all_moments P B π hπ hπp K x r μ σ T hK hb hx
  have hNm := half_local_joint_measurable P B.F B.le N hN
  have hDm := half_local_joint_measurable P B.F B.le _ hC.defect
  have hCm : Measurable (fun z : Ω × ℝ => C (realTimeClamp z.2) z.1) := by
    convert (hNm.mul hNm).sub hDm using 1
    funext z
    simp only [Pi.sub_apply,Pi.mul_apply]
    ring
  have hVm : Measurable (fun z : Ω × ℝ => x*Real.exp ((∫ s in 0..z.2,r+π (z.1,s)*(μ-r))+N (realTimeClamp z.2) z.1-C (realTimeClamp z.2) z.1/2)) :=
    (((time_primitive_joint_measurable _ (measurable_const.add (hπ.mul_const (μ-r)))).add hNm).sub (hCm.div_const 2)).exp.const_mul x
  refine ⟨N,C,hN,hNI,hC,hCe,hVm,fun z => mul_pos hx (Real.exp_pos _),?_⟩
  intro q
  exact uniform_moments_time_integrable P _ hVm (fun z => mul_pos hx (Real.exp_pos _)) q T
    (x^q*Real.exp (|q| *((|r|+K*|μ-r|)*T)+|q^2-q| *((|σ| *K)^2*T)/2))
    (fun t ht => (hmom q t ht).1) (fun t ht => (hmom q t ht).2)

end Asakura.Chapter11
