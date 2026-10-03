import Chapter9DensityProductBracket

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Ito's product formula with the actual time-density drift integrals.
The remaining process is constructed as a sum of Ito integrals. -/
theorem density_product_with_integrals {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y A B M N C : HalfClosedTime → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y B N)
    (hC : LocalCovarianceWitness P F M N C)
    (ξ η : Ω → ℝ) (G H : Ω × ℝ → ℝ)
    (hGm : ∀ w,Measurable (fun r => G (w,r))) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hGi : ∀ r,0≤r → ∀ w,IntervalIntegrable (fun u => G (w,u)) volume 0 r)
    (hHi : ∀ r,0≤r → ∀ w,IntervalIntegrable (fun u => H (w,u)) volume 0 r)
    (hA : ∀ r,0≤r → ∀ w,A (realTimeClamp r) w=ξ w+∫ u in 0..r,G (w,u))
    (hB : ∀ r,0≤r → ∀ w,B (realTimeClamp r) w=η w+∫ u in 0..r,H (w,u)) :
    ∃ J L : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P F J ∧ LocalMProcessWitness P F L ∧
      ItoCovarianceFormula P F M (fun z => Y (realTimeClamp z.2) z.1) J ∧
      ItoCovarianceFormula P F N (fun z => X (realTimeClamp z.2) z.1) L ∧
      ∀ r,0≤r → ∀ᵐ w ∂P,
        X (realTimeClamp r) w*Y (realTimeClamp r) w = X ⊥ w*Y ⊥ w+
          (∫ u in 0..r,Y (realTimeClamp u) w*G (w,u))+
          (∫ u in 0..r,X (realTimeClamp u) w*H (w,u))+C (realTimeClamp r) w+(J (realTimeClamp r) w+L (realTimeClamp r) w) := by
  have hXa t (ht : t<⊤) : Measurable[F t] (X t) := by
    have he : X t=(fun w => A t w+M t w) := funext (hX.decomposition t ht)
    rw [he]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  have hYa t (ht : t<⊤) : Measurable[F t] (Y t) := by
    have he : Y t=(fun w => B t w+N t w) := funext (hY.decomposition t ht)
    rw [he]
    exact (hY.variation.adapted t ht).add (hY.martingale.adapted P F t ht)
  have hXr w : Continuous (fun r : ℝ => X (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hX.continuous w _ (by
      apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
      exact real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _))).comp real_time_clamp_continuous.continuousAt
  have hYr w : Continuous (fun r : ℝ => Y (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hY.continuous w _ (by
      apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
      exact real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _))).comp real_time_clamp_continuous.continuousAt
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion (T := (⊤:EReal)) (by simp)
  obtain ⟨I,J,hIJ,hI,hJ⟩ := continuous_semimartingale_integral_exists P (by simp) F hF hle hnull
    X A M Y hX hYa hY.continuous c (fun n => (hc n).le) hcm.monotone hcT hcc
  obtain ⟨K,L,hKL,hK,hL⟩ := continuous_semimartingale_integral_exists P (by simp) F hF hle hnull
    Y B N X hY hXa hX.continuous c (fun n => (hc n).le) hcm.monotone hcT hcc
  have hp := semimartingale_product_formula P (by simp) F hF hle hnull X Y A B M N C
    (fun t w => I t w+J t w) (fun t w => K t w+L t w) hX hY hC c (fun n => (hc n).le) hcT hcc
    ⟨I,J,hIJ,hI,hJ⟩ ⟨K,L,hKL,hK,hL⟩
  refine ⟨J,L,hIJ.martingale,hKL.martingale,hJ,hL,?_⟩
  intro r hr
  have hi := time_density_variation_integral_with_initial P A I ξ G
    (fun z => Y (realTimeClamp z.2) z.1) c (fun n => (hc n).le) hcT hcc
    (fun n => ae_of_all _ fun w u hu => hA u hu.1 w) hGm
    (fun n => ae_of_all _ (hGi _ (hc n).le)) (fun w => (hYr w).measurable)
    (fun _ w => (hYr w).continuousOn) hI r hr (EReal.coe_lt_top r)
  have hk := time_density_variation_integral_with_initial P B K η H
    (fun z => X (realTimeClamp z.2) z.1) c (fun n => (hc n).le) hcT hcc
    (fun n => ae_of_all _ fun w u hu => hB u hu.1 w) hHm
    (fun n => ae_of_all _ (hHi _ (hc n).le)) (fun w => (hXr w).measurable)
    (fun _ w => (hXr w).continuousOn) hK r hr (EReal.coe_lt_top r)
  filter_upwards [hp,hi,hk] with w hpw hiw hkw
  have he := hpw (realTimeClamp r) (real_time_below r hr (EReal.coe_lt_top r))
  rw [hiw,hkw] at he
  linarith

end Asakura.Chapter10
