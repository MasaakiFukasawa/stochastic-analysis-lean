import Chapter11LinearSDEFormula
import Chapter11BoundedStrategyIntegral
import Chapter11FiniteSDEDecomposition
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- The Brownian linear SDE has the printed exponential form for every
 solution. The coefficient is extended by zero after the finite horizon;
 neither positivity of the solution nor its exponential form is assumed. -/
theorem brownian_linear_sde_formula {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b H : Ω × ℝ → ℝ) (hbm : Measurable b) (hHm : Measurable H)
    (hbp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => b (z.1,z.2.val)))
    (hHp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (L K R : ℝ) (hK : 0≤K) (hbb : ∀ z,|b z|≤L) (hHb : ∀ z,|H z|≤K)
    (hR : 0<R) (hzero : ∀ w s,R<s → b (w,s)=0)
    (X A M : HalfClosedTime → Ω → ℝ) (hX : SemimartingaleDecomposition P B.F X A M)
    (hMI : ItoCovarianceFormula P B.F (B.W 0) (fun z => X (realTimeClamp z.2) z.1*H z) M)
    (hAe : ∀ᵐ w ∂P,∀ s,0≤s → A (realTimeClamp s) w=A ⊥ w+
      ∫ t in 0..s,X (realTimeClamp t) w*b (w,t)) :
    ∃ D : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F D ∧ ItoCovarianceFormula P B.F (B.W 0) H D ∧
      ∀ t,0≤t → X (realTimeClamp t)=ᵐ[P] fun w => X ⊥ w*
        Real.exp ((∫ s in 0..t,b (w,s)-(H (w,s))^2/2)+D (realTimeClamp t) w) := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨D,Q,hD,hDI,hQ,hQe,_,_,_⟩ := bounded_strategy_integral P B H hHm hHp K hK hHb
  have hbi w d (hd : 0≤d) := bounded_time_integrable _ (hbm.comp measurable_prodMk_left) L (fun s => hbb (w,s)) d hd
  have hqi w d (hd : 0≤d) : IntervalIntegrable (fun s => (H (w,s))^2) volume 0 d := by
    simpa only [pow_two,Function.comp_def] using bounded_product_time_integrable _ _
      (hHm.comp measurable_prodMk_left) (hHm.comp measurable_prodMk_left) K hK
      (fun s => hHb (w,s)) (fun s => hHb (w,s)) d hd
  obtain ⟨J,hJ,hJc,hJe⟩ := progressive_integrable_drift_variation hT B.F B.mono R hR.le le_top b
    (hbp R hR) (fun w => (hbi w R hR.le).1)
  have hJe' w t (ht : 0≤t) : J (realTimeClamp t) w=∫ s in 0..t,b (w,s) := by
    rw [hJe,finite_prefix_time_min R t hR.le ht le_top]
    rw [←clipped_driver_integral (fun s => b (w,s)) R t hR.le ht]
    apply intervalIntegral.integral_congr
    intro s hs
    by_cases hsR : s≤R
    · simp only [mem_Iic,hsR,indicator_of_mem]
    · rw [indicator_of_notMem (show s∉Iic R from hsR)]
      exact (hzero w s (lt_of_not_ge hsR)).symm
  have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T:=(⊤:EReal)) 0:EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
  have hJ0 w : J ⊥ w=0 := by simpa only [hz,intervalIntegral.integral_same] using hJe' w 0 le_rfl
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  have hXa t (ht : t<⊤) : Measurable[B.F t] (X t) := by
    have he : X t=fun w => A t w+M t w := funext (hX.decomposition t ht)
    rw [he]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P B.F t ht)
  obtain ⟨hra,hrc⟩ := open_process_real_regularity B.F X hXa hX.continuous
  obtain ⟨U,hU,hUI⟩ := continuous_adapted_ito_exists P hT B.F B.mono B.le B.null D hD
    (fun z => X (realTimeClamp z.2) z.1) hra hrc
  have hassoc := ito_integral_associativity P hT B.F B.mono B.le B.null (B.W 0) D U M
    H (fun z => X (realTimeClamp z.2) z.1) (B.martingale 0) hD hU hX.martingale
    (fun w => hHm.comp measurable_prodMk_left) (fun w => open_path_real_measurable _ (hX.continuous w)) hDI hUI hMI
  have hMI' : ItoCovarianceFormula P B.F D (fun z => X (realTimeClamp z.2) z.1) M :=
    ItoCovarianceFormula.congr_integral P B.F B.mono B.le D U M _ hU hX.martingale hassoc hUI
  have hQc := local_covariance_path_continuous P B.F D D Q hD hD hQ
  have hQv := covariance_adapted_variation P B.F B.mono B.le hD hD hQ
  have hQcomm n := bracket_primitive_common_time P (c n) (hc n).le
    (fun t => Q (realTimeClamp t)) (fun w t => (H (w,t))^2)
    ((open_process_real_regularity B.F Q hQv.adapted hQc).2 (c n) (hc n).le (hcT n))
    (ae_of_all _ fun w => hqi w (c n) (hc n).le) (fun s hs => hQe s hs.1)
  have hf := linear_sde_exponential_formula P hT B.F B.mono B.le B.null D Q J hD hQ hJ
    (fun w t _ => (hJc w).continuousAt) X A M hX hMI' (ae_of_all _ hJ0)
    c hc hcm.monotone hcT hcc b (fun z => (H z)^2)
    (fun w => hbm.comp measurable_prodMk_left) (fun w => (hHm.comp measurable_prodMk_left).pow_const 2)
    (fun n => ae_of_all _ fun w => hbi w (c n) (hc n).le)
    (fun n => ae_of_all _ fun w => hqi w (c n) (hc n).le)
    (fun n => ae_of_all _ fun w s hs => by rw [hJ0,zero_add];exact hJe' w s hs.1)
    hQcomm (fun n => hAe.mono fun w hw s hs => hw s hs.1)
  refine ⟨D,hD,hDI,?_⟩
  intro t ht
  filter_upwards [hf t ht (EReal.coe_lt_top t),hQe t ht] with w hw hq
  rw [hw,hJe' w t ht,hq]
  congr 2
  have hi : IntervalIntegrable (fun s => b (w,s)) volume 0 t := hbi w t ht
  rw [intervalIntegral.integral_sub hi ((hqi w t ht).div_const 2),intervalIntegral.integral_div]

end Asakura.Chapter11
