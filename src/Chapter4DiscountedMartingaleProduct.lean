import Chapter4DiscountProcess
import Chapter5TimeDensityVariation
import Chapter5ClippedDriftIntegral
import Chapter4DiscountCalculus
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The discount factor applied to the local martingale part has the
actual stochastic product formula with its time drift identified. -/
theorem discounted_martingale_product
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (N K : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (hKa : ∀ t,t<⊤ → Measurable[F t] (K t))
    (hKc : ∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hKpos : ∀ w r,r∈Icc 0 R → 0≤K (realTimeClamp r) w) :
    ∃ Z : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F Z ∧
      ∀ r∈Icc 0 R,
        (fun w => N (realTimeClamp r) w*discountFactor (fun s => K (realTimeClamp s) w) r)=ᵐ[P]
        fun w => Z (realTimeClamp r) w-
          ∫ s in 0..r,N (realTimeClamp s) w*discountFactor (fun u => K (realTimeClamp u) w) s*K (realTimeClamp s) w := by
  obtain ⟨A,hA,hAc,hAe,hAm,hD,_⟩ := nonnegative_discount_process hT F hF K hKa hKc R hR hRT hKpos
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  have hv : ContDiff ℝ 1 (fun x : ℝ => Real.exp (-x)) := by fun_prop
  have hder x : deriv (fun x : ℝ => Real.exp (-x)) x= -Real.exp (-x) := by
    simpa only [neg_one_mul,mul_neg,mul_one,Pi.neg_apply,id_eq] using ((hasDerivAt_id x).neg.exp).deriv
  obtain ⟨Z,L,hZ,hZI,hL,hLc,hLI,hprod⟩ := C1_weighted_product_constructed P hT F hF hle hnull
    N A hN hA (fun w t _ => (hAc w).continuousAt) _ hv hD
    c (fun n => (hc n).le) hcm.monotone hcT hcc
  simp only [hder] at hLI
  let G := fun z : Ω × ℝ => (Iic R).indicator (fun r => K (realTimeClamp r) z.1) z.2
  have hGm w : Measurable (fun r => G (w,r)) :=
    (open_path_real_measurable _ (hKc w)).indicator measurableSet_Iic
  have hGi n : ∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)) volume 0 (c n) := by
    apply ae_of_all
    intro w
    have hi := ((open_process_real_regularity F K hKa hKc).2 (c n) (hc n).le (hcT n) w).intervalIntegrable_of_Icc (μ:=volume) (hc n).le
    exact ⟨hi.1.indicator measurableSet_Iic,hi.2.indicator measurableSet_Iic⟩
  have hAG n : ∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A (realTimeClamp r) w=∫ s in 0..r,G (w,s) := by
    apply ae_of_all
    intro w r hr
    rw [hAe,finite_prefix_time_min R r hR hr.1 ((EReal.coe_le_coe hr.2).trans (hcT n).le)]
    dsimp only [G]
    rw [clipped_driver_integral _ R r hR hr.1]
  let H := fun z : Ω × ℝ => N (realTimeClamp z.2) z.1*(-Real.exp (-A (realTimeClamp z.2) z.1))
  have hHa t ht : Measurable[F t] (fun w => N t w*(-Real.exp (-A t w))) :=
    (hN.adapted P F t ht).mul (((hA.adapted t ht).neg.exp).neg)
  have hHc w t ht : ContinuousAt (fun s => N s w*(-Real.exp (-A s w))) t :=
    (hN.path P F w t ht).mul ((Real.continuous_exp.continuousAt.comp (hAc w).continuousAt.neg).neg)
  have hHm w : Measurable (fun r => H (w,r)) := open_path_real_measurable _ (hHc w)
  have hHcc n w : ContinuousOn (fun r => H (w,r)) (Icc 0 (c n)) :=
    (open_process_real_regularity F _ hHa hHc).2 (c n) (hc n).le (hcT n) w
  refine ⟨Z,hZ,?_⟩
  intro r hr
  have hrT := (EReal.coe_le_coe hr.2).trans_lt hRT
  have ht := time_density_variation_integral P A L G H c (fun n => (hc n).le) hcT hcc
    hAG hGm hGi hHm hHcc hLI r hr.1 hrT
  filter_upwards [hprod,ht] with w hp ht
  have hp' := hp _ (real_time_below r hr.1 hrT)
  rw [ht] at hp'
  have hAd s (hs : s∈Icc 0 R) : Real.exp (-A (realTimeClamp s) w)=
      discountFactor (fun u => K (realTimeClamp u) w) s := by
    rw [hAe,finite_prefix_time_of_real R s hR hs hRT.le]
    rfl
  rw [hAd r hr] at hp'
  have hint : (∫ s in 0..r,H (w,s)*G (w,s))=
      -(∫ s in 0..r,N (realTimeClamp s) w*discountFactor (fun u => K (realTimeClamp u) w) s*K (realTimeClamp s) w) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s∈Icc 0 R := Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using hs)
    dsimp only [H,G]
    rw [Set.indicator_of_mem (show s∈Iic R from hs'.2),hAd s hs']
    ring
  rw [hint] at hp'
  exact hp'

end Asakura.Chapter4
