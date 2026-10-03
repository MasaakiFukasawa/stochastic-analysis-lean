import Chapter11BrownianLinearFormula
import Chapter11PositiveTimeIntegral
import Chapter11DiscountIntegrability
import Chapter5StoppedIntegralFormula
import Chapter5ProgressiveZeroExtension

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

/-- The finite-horizon linear SDE in the manuscript. Its integral equation
 constructs a stopped semimartingale; the inverse-factor proof then gives
 the exponential formula through the endpoint, without a positivity premise. -/
theorem finite_linear_sde_formula {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (R : ℝ) (hR : 0<R) (b H : Ω × ℝ → ℝ) (hbm : Measurable b) (hHm : Measurable H)
    (hbp : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => b (z.1,z.2.val)))
    (hHp : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)))
    (L K : ℝ) (hL : 0≤L) (hK : 0≤K) (hbb : ∀ z,|b z|≤L) (hHb : ∀ z,|H z|≤K)
    (X N : HalfClosedTime → Ω → ℝ) (ξ : Ω → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (hXa : ∀ t,t<⊤ → Measurable[B.F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => X (realTimeClamp z.2) z.1*H z) N)
    (he : ∀ᵐ w ∂P,∀ t∈Icc 0 R,X (realTimeClamp t) w=ξ w+
      (∫ s in 0..t,X (realTimeClamp s) w*b (w,s))+N (realTimeClamp t) w) :
    ∃ D : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F D ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => (Iic R).indicator (fun s => H (z.1,s)) z.2) D ∧
      ∀ t∈Icc 0 R,X (realTimeClamp t)=ᵐ[P] fun w => ξ w*
        Real.exp ((∫ s in 0..t,b (w,s)-(H (w,s))^2/2)+D (realTimeClamp t) w) := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨hra,hrc⟩ := open_process_real_regularity B.F X hXa hXc
  have hXp := continuous_adapted_real_progressive B.F B.mono
    (fun z => X (realTimeClamp z.2) z.1) R hR.le
    (fun s hs => hra s hs.1 (EReal.coe_lt_top s)) (hrc R hR.le (EReal.coe_lt_top R))
  have hbi w : Integrable (fun s => X (realTimeClamp s) w*b (w,s)) (volume.restrict (Ioc 0 R)) := by
    exact continuous_multiplier_integrable R hR.le _
      ((ae_restrict_mem measurableSet_Ioc).mono fun s hs => ⟨hs.1.le,hs.2⟩)
      (fun s => X (realTimeClamp s) w) (fun s => b (w,s))
      (hrc R hR.le (EReal.coe_lt_top R) w) (open_path_real_measurable _ (hXc w))
      (bounded_time_integrable _ (hbm.comp measurable_prodMk_left) L (fun s => hbb (w,s)) R hR.le).1
  obtain ⟨A,M,hXs,hAe,hMe,hAall⟩ := finite_sde_decomposition P B R hR.le X N ξ hξ hXa hXc hN
    (fun z => X (realTimeClamp z.2) z.1*b z) (hXp.mul hbp) hbi he
  let Y := fun t w => X (min (realTimeClamp R) t) w
  let bc := fun z : Ω × ℝ => (Iic R).indicator (fun s => b (z.1,s)) z.2
  let Hc := fun z : Ω × ℝ => (Iic R).indicator (fun s => H (z.1,s)) z.2
  have hbc : Measurable bc := by
    change Measurable ((Prod.snd ⁻¹' Iic R).indicator b)
    exact hbm.indicator (measurableSet_Iic.preimage measurable_snd)
  have hHc : Measurable Hc := by
    change Measurable ((Prod.snd ⁻¹' Iic R).indicator H)
    exact hHm.indicator (measurableSet_Iic.preimage measurable_snd)
  have hFreal : Monotone (fun s : ℝ => B.F (realTimeClamp s)) := fun s t hst => B.mono (real_time_clamp_mono hst)
  have hbcp d (_hd : 0<d) := progressive_finite_zero_extension _ hFreal R hR.le b hbp d
  have hHcp d (_hd : 0<d) := progressive_finite_zero_extension _ hFreal R hR.le H hHp d
  have hbcb z : |bc z|≤L := by
    dsimp only [bc]
    by_cases hz : z.2∈Iic R
    · rw [indicator_of_mem hz];exact hbb z
    · rw [indicator_of_notMem hz,abs_zero];exact hL
  have hHcb z : |Hc z|≤K := by
    dsimp only [Hc]
    by_cases hz : z.2∈Iic R
    · rw [indicator_of_mem hz];exact hHb z
    · rw [indicator_of_notMem hz,abs_zero];exact hK
  have hstop : ∀ t,MeasurableSet[B.F t] {w : Ω | realTimeClamp R≤t} := by
    intro t
    by_cases ht : realTimeClamp (T:=(⊤:EReal)) R≤t <;> simp [ht]
  have hNs := hN.stopped P B.F B.mono B.le (fun _ => realTimeClamp R) hstop
  have hst := stopped_ito_covariance_formula P hT B.F B.mono B.le B.null (B.W 0) N
    (fun z => X (realTimeClamp z.2) z.1*H z) (B.martingale 0) hN
    (fun w => (open_path_real_measurable _ (hXc w)).mul (hHm.comp measurable_prodMk_left)) hNI R hR.le
  have hst' : ItoCovarianceFormula P B.F (B.W 0) (fun z => Y (realTimeClamp z.2) z.1*Hc z)
      (fun t w => N (min (realTimeClamp R) t) w) := by
    apply ItoCovarianceFormula.congr_on_positive_time_domain P B.F _ _ _ _ hst
    intro w s hs _
    dsimp only [Y,Hc]
    by_cases hsR : s≤R
    · rw [indicator_of_mem (show s∈Ioc 0 R from ⟨hs,hsR⟩),indicator_of_mem (show s∈Iic R from hsR),
        min_eq_right (real_time_clamp_mono hsR)]
    · rw [indicator_of_notMem (show s∉Ioc 0 R from fun h => hsR h.2),
        indicator_of_notMem (show s∉Iic R from hsR),mul_zero]
  have hMI : ItoCovarianceFormula P B.F (B.W 0) (fun z => Y (realTimeClamp z.2) z.1*Hc z) M :=
    ItoCovarianceFormula.congr_integral P B.F B.mono B.le _ _ _ _ hNs hXs.martingale
      (hMe.mono fun w hw t ht => (hw t ht).symm) hst'
  have hAeq : ∀ᵐ w ∂P,∀ s,0≤s → A (realTimeClamp s) w=A ⊥ w+
      ∫ t in 0..s,Y (realTimeClamp t) w*bc (w,t) := by
    apply ae_of_all
    intro w s hs
    rw [hAall w s hs]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [Y,bc]
    by_cases htR : t≤R
    · rw [indicator_of_mem (show t∈Iic R from htR),indicator_of_mem (show t∈Iic R from htR),
        min_eq_right (real_time_clamp_mono htR)]
    · rw [indicator_of_notMem (show t∉Iic R from htR),indicator_of_notMem (show t∉Iic R from htR),mul_zero]
  obtain ⟨D,hD,hDI,hDe⟩ := brownian_linear_sde_formula P B bc Hc hbc hHc hbcp hHcp L K R hK hbcb hHcb hR
    (fun w s hs => indicator_of_notMem (show s∉Iic R from not_le.mpr hs) _) Y A M hXs hMI hAeq
  have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T:=(⊤:EReal)) 0:EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
  have hinit : X ⊥=ᵐ[P] ξ := by
    filter_upwards [he,hN.initial P B.F] with w hw hn
    simpa only [hz,intervalIntegral.integral_same,add_zero,hn,Pi.zero_apply] using hw 0 ⟨le_rfl,hR.le⟩
  refine ⟨D,hD,hDI,?_⟩
  intro t ht
  filter_upwards [hDe t ht.1,hinit] with w hw hi
  have hYt : Y (realTimeClamp t) w=X (realTimeClamp t) w := by
    dsimp only [Y];rw [min_eq_right (real_time_clamp_mono ht.2)]
  have hY0 : Y ⊥ w=ξ w := by dsimp only [Y];rw [min_eq_right bot_le,hi]
  rw [hYt,hY0] at hw
  rw [hw]
  congr 2
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hsR : s≤R := (show s∈Icc 0 t by simpa only [uIcc_of_le ht.1] using hs).2.trans ht.2
  dsimp only [bc,Hc]
  rw [indicator_of_mem (show s∈Iic R from hsR),indicator_of_mem (show s∈Iic R from hsR)]

end Asakura.Chapter11
