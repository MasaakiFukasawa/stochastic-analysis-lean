import Chapter11LogWealthConstruction
import Chapter11ExponentialDrift
import Chapter11BrownianAssociativity

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The exponential wealth equation for bounded progressive drift and
volatility. This constructs its Brownian integral, rather than assuming an
Ito decomposition of the claimed exponential solution. -/
theorem exponential_bounded_sde_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b H : Ω × ℝ → ℝ) (hbm : Measurable b) (hHm : Measurable H)
    (hbp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => b (z.1,z.2.val)))
    (hHp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (K L x R : ℝ) (hK : 0≤K) (hHb : ∀ z,|H z|≤K) (hbb : ∀ z,|b z|≤L) (hR : 0<R) :
    ∃ V N M : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F N ∧ LocalMProcessWitness P B.F M ∧
      ItoCovarianceFormula P B.F (B.W 0) H N ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => V (realTimeClamp z.2) z.1*H z) M ∧
      (∀ w t,0<V t w) ∧
      (∀ w t,t∈Icc 0 R → V (realTimeClamp t) w=Real.exp (x+(∫ s in 0..t,b (w,s))+N (realTimeClamp t) w)) ∧
      (∀ t∈Icc 0 R,V (realTimeClamp t)=ᵐ[P]
        fun w => Real.exp x+(∫ s in 0..t,V (realTimeClamp s) w*(b (w,s)+(H (w,s))^2/2))+M (realTimeClamp t) w) ∧
      (∀ t,t<⊤ → Measurable[B.F t] (V t)) ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => V s w) t) := by
  obtain ⟨X,A,N,C,hX,hNI,hC,hA0,hAe,hCe,hX0⟩ := logarithmic_wealth_constructed P B b H hbm hHm hbp hHp K L x R hK hHb hbb hR
  have hbi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 R :=
    ae_of_all _ fun w => bounded_time_integrable _ (hbm.comp measurable_prodMk_left) L (fun r => hbb (w,r)) R hR.le
  have hqi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => (H (w,r))^2) volume 0 R := by
    apply ae_of_all
    intro w
    simpa only [pow_two,Function.comp_def] using bounded_product_time_integrable _ _
      (hHm.comp measurable_prodMk_left) (hHm.comp measurable_prodMk_left) K hK (fun r => hHb (w,r)) (fun r => hHb (w,r)) R hR.le
  obtain ⟨L₀,hL₀,hL₀I,he⟩ := exponential_time_drift_constructed P (by simp) B.F B.mono B.le B.null
    X A N C hX hC b (fun z => (H z)^2) (fun w => hbm.comp measurable_prodMk_left)
    (fun w => (hHm.comp measurable_prodMk_left).pow_const 2) R hR.le (EReal.coe_lt_top R) hbi hqi
    (ae_of_all _ fun w r hr => by rw [hA0];exact hAe w r hr) hCe
  let V := fun t w => Real.exp (X t w)
  have hVa t (ht : t<⊤) : Measurable[B.F t] (V t) := by
    have hh : X t=(fun w => A t w+N t w) := funext (hX.decomposition t ht)
    dsimp only [V]
    rw [hh]
    exact ((hX.variation.adapted t ht).add (hX.martingale.adapted P B.F t ht)).exp
  have hVc w t ht : ContinuousAt (fun s => V s w) t := Real.continuous_exp.continuousAt.comp (hX.continuous w t ht)
  obtain ⟨Z,M,hZ,hM,hZI,hMI,hZM⟩ := bounded_brownian_integral_continuous_weight P B H hHm hHp K hK hHb N V hX.martingale hNI hVa hVc
  have hLZ := hL₀I.unique P (by simp) B.F B.mono B.le B.null N L₀ Z _ hX.martingale hL₀ hZ hZI
  refine ⟨V,N,M,hX.martingale,hM,hNI,hMI,fun _ _ => Real.exp_pos _,?_,?_,hVa,hVc⟩
  · intro w t ht
    dsimp only [V]
    rw [hX.decomposition _ (real_time_below t ht.1 (EReal.coe_lt_top t)),hAe w t ht]
  · intro t ht
    filter_upwards [he t ht,hLZ,hZM,hX0] with w he hl hz h0
    have ht' := real_time_below t ht.1 (EReal.coe_lt_top t)
    rw [h0,hl _ ht',hz _ ht'] at he
    exact he

end Asakura.Chapter11
