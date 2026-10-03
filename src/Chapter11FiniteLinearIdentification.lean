import Chapter11FiniteLinearSDE

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency false

/-- Identify the finite-horizon solution with the original, un-stopped
 coefficient integral. Its restriction agrees with the zero extension's
 integral by actual Ito uniqueness, including at maturity. -/
theorem finite_linear_original_noise_formula {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (R : ℝ) (hR : 0<R) (b H : Ω × ℝ → ℝ) (hbm : Measurable b) (hHm : Measurable H)
    (hbp : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => b (z.1,z.2.val)))
    (hHp : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)))
    (L K : ℝ) (hL : 0≤L) (hK : 0≤K) (hbb : ∀ z,|b z|≤L) (hHb : ∀ z,|H z|≤K)
    (X N D : HalfClosedTime → Ω → ℝ) (ξ : Ω → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (hXa : ∀ t,t<⊤ → Measurable[B.F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => X (realTimeClamp z.2) z.1*H z) N)
    (hD : LocalMProcessWitness P B.F D) (hDI : ItoCovarianceFormula P B.F (B.W 0) H D)
    (he : ∀ᵐ w ∂P,∀ t∈Icc 0 R,X (realTimeClamp t) w=ξ w+
      (∫ s in 0..t,X (realTimeClamp s) w*b (w,s))+N (realTimeClamp t) w) :
    ∀ t∈Icc 0 R,X (realTimeClamp t)=ᵐ[P] fun w => ξ w*
      Real.exp ((∫ s in 0..t,b (w,s)-(H (w,s))^2/2)+D (realTimeClamp t) w) := by
  obtain ⟨E,hE,hEI,hform⟩ := finite_linear_sde_formula P B R hR b H hbm hHm hbp hHp
    L K hL hK hbb hHb X N ξ hξ hXa hXc hN hNI he
  have hs : ∀ t,MeasurableSet[B.F t] {w : Ω | realTimeClamp R≤t} := by
    intro t
    by_cases ht : realTimeClamp (T:=(⊤:EReal)) R≤t <;> simp [ht]
  have hDs := hD.stopped P B.F B.mono B.le (fun _ => realTimeClamp R) hs
  have hDI' := stopped_ito_covariance_formula P (by simp) B.F B.mono B.le B.null (B.W 0) D H
    (B.martingale 0) hD (fun w => hHm.comp measurable_prodMk_left) hDI R hR.le
  have hDI'' : ItoCovarianceFormula P B.F (B.W 0)
      (fun z => (Iic R).indicator (fun s => H (z.1,s)) z.2)
      (fun t w => D (min (realTimeClamp R) t) w) := by
    apply ItoCovarianceFormula.congr_on_positive_time_domain P B.F _ _ _ _ hDI'
    intro w s hs _
    by_cases hsR : s≤R
    · rw [indicator_of_mem (show s∈Ioc 0 R from ⟨hs,hsR⟩),indicator_of_mem (show s∈Iic R from hsR)]
    · rw [indicator_of_notMem (show s∉Ioc 0 R from fun h => hsR h.2),indicator_of_notMem (show s∉Iic R from hsR)]
  have huniq := hEI.unique P (by simp) B.F B.mono B.le B.null (B.W 0) E
    (fun t w => D (min (realTimeClamp R) t) w) _ (B.martingale 0) hE hDs hDI''
  intro t ht
  filter_upwards [hform t ht,huniq] with w hw hu
  rw [hw,hu _ (real_time_below t ht.1 (EReal.coe_lt_top t)),min_eq_right (real_time_clamp_mono ht.2)]

end Asakura.Chapter11
