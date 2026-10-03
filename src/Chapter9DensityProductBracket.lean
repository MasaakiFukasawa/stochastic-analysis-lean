import Chapter9BracketIdentification
import Chapter9FiniteIntervalMartingale
import Chapter3ProductFormula
import Chapter3ContinuousIntegralConstruction
import Chapter5TimeDensityInitial
import Chapter4FinitePathLift

open MeasureTheory Set Filter
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the two stochastic integrals in the product formula and
 identify the bracket from the coordinate-product martingale. -/
theorem density_product_bracket {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y A B M N Q D : HalfClosedTime → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y B N)
    (G H : Ω × ℝ → ℝ)
    (hGm : ∀ w,Measurable (fun r => G (w,r))) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hGi : ∀ r,0≤r → ∀ w,IntervalIntegrable (fun u => G (w,u)) volume 0 r)
    (hHi : ∀ r,0≤r → ∀ w,IntervalIntegrable (fun u => H (w,u)) volume 0 r)
    (hA : ∀ r,0≤r → ∀ w,A (realTimeClamp r) w=X ⊥ w+∫ u in 0..r,G (w,u))
    (hB : ∀ r,0≤r → ∀ w,B (realTimeClamp r) w=Y ⊥ w+∫ u in 0..r,H (w,u))
    (hQ : LocalMProcessWitness P F Q) (hD : LocalVariationWitness F D)
    (hDm : ∀ t,Measurable[F t] (D t)) (hDc : ∀ w,Continuous (fun t => D t w))
    (hQform : ∀ r,0≤r → ∀ w,Q (realTimeClamp r) w=
      X (realTimeClamp r) w*Y (realTimeClamp r) w-X ⊥ w*Y ⊥ w-
        (∫ u in 0..r,Y (realTimeClamp u) w*G (w,u))-
        (∫ u in 0..r,X (realTimeClamp u) w*H (w,u))-D (realTimeClamp r) w) :
    LocalCovarianceWitness P F M N D := by
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
  obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull M N hX.martingale hY.martingale
  have hp := semimartingale_product_formula P (by simp) F hF hle hnull X Y A B M N C
    (fun t w => I t w+J t w) (fun t w => K t w+L t w) hX hY hC c (fun n => (hc n).le) hcT hcc
    ⟨I,J,hIJ,hI,hJ⟩ ⟨K,L,hKL,hK,hL⟩
  apply bracket_from_product_identity_pointwise P (by simp) F hF hle M N C D Q J L
    hX.martingale hY.martingale hC hD hDm hDc hQ hIJ.martingale hKL.martingale
  intro t ht
  obtain ⟨r,hr,_,rfl⟩ := finite_closed_time_real t ht
  have hi := time_density_variation_integral_with_initial P A I (X ⊥) G
    (fun z => Y (realTimeClamp z.2) z.1) c (fun n => (hc n).le) hcT hcc
    (fun n => ae_of_all _ fun w u hu => hA u hu.1 w) hGm
    (fun n => ae_of_all _ (hGi _ (hc n).le)) (fun w => (hYr w).measurable)
    (fun _ w => (hYr w).continuousOn) hI r hr (EReal.coe_lt_top r)
  have hk := time_density_variation_integral_with_initial P B K (Y ⊥) H
    (fun z => X (realTimeClamp z.2) z.1) c (fun n => (hc n).le) hcT hcc
    (fun n => ae_of_all _ fun w u hu => hB u hu.1 w) hHm
    (fun n => ae_of_all _ (hHi _ (hc n).le)) (fun w => (hXr w).measurable)
    (fun _ w => (hXr w).continuousOn) hK r hr (EReal.coe_lt_top r)
  filter_upwards [hp,hi,hk] with w hpw hiw hkw
  have he := hpw (realTimeClamp r) (by
      apply (real_time_clamp_mono (le_max_left r 0)).trans_lt
      exact real_time_below (max r 0) (le_max_right r 0) (EReal.coe_lt_top _))
  rw [hQform r hr w]
  rw [hiw,hkw] at he
  linarith
end Asakura.Chapter9
