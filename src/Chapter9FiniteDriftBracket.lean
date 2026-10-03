import Chapter9DensityProductBracket
import Chapter9DriftSemimartingale
import Chapter9FrozenDriftIntegrals

open MeasureTheory Set
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- A continuous finite-strip diffusion characterized by its coordinate
 and coordinate-product tests has the claimed constant bracket density. -/
theorem finite_drift_bracket {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (Z V a v : ℝ → Ω → ℝ) (b : ℝ) (hb : 0≤b) (c : ℝ)
    (hZ0 : Measurable[F ⊥] (Z 0)) (hV0 : Measurable[F ⊥] (V 0))
    (hZc : ∀ w,ContinuousOn (fun r => Z r w) (Icc 0 b))
    (hVc : ∀ w,ContinuousOn (fun r => V r w) (Icc 0 b))
    (ha : ∀ r∈Icc 0 b,Measurable[F (realTimeClamp r)] (a r))
    (hv : ∀ r∈Icc 0 b,Measurable[F (realTimeClamp r)] (v r))
    (ham : ∀ w,Measurable (fun r => a r w)) (hvm : ∀ w,Measurable (fun r => v r w))
    (hac : ∀ w,ContinuousOn (fun r => a r w) (Icc 0 b))
    (hvc : ∀ w,ContinuousOn (fun r => v r w) (Icc 0 b))
    (hM : LocalMProcessWitness P F (fun t w =>
      Z (finitePrefixTime b hb t).val w-Z 0 w-∫ r in 0..(finitePrefixTime b hb t).val,a r w))
    (hN : LocalMProcessWitness P F (fun t w =>
      V (finitePrefixTime b hb t).val w-V 0 w-∫ r in 0..(finitePrefixTime b hb t).val,v r w))
    (hQ : LocalMProcessWitness P F (fun t w =>
      Z (finitePrefixTime b hb t).val w*V (finitePrefixTime b hb t).val w-Z 0 w*V 0 w-
        ∫ r in 0..(finitePrefixTime b hb t).val,V r w*a r w+Z r w*v r w+c)) :
    LocalCovarianceWitness P F
      (fun t w => Z (finitePrefixTime b hb t).val w-Z 0 w-∫ r in 0..(finitePrefixTime b hb t).val,a r w)
      (fun t w => V (finitePrefixTime b hb t).val w-V 0 w-∫ r in 0..(finitePrefixTime b hb t).val,v r w)
      (fun t _ => c*(finitePrefixTime b hb t).val) := by
  let p := fun t : HalfClosedTime => (finitePrefixTime b hb t).val
  let X := fun t w => Z (p t) w
  let Y := fun t w => V (p t) w
  let A := fun t w => Z 0 w+∫ r in 0..p t,a r w
  let B := fun t w => V 0 w+∫ r in 0..p t,v r w
  let G := fun z : Ω × ℝ => (Iic b).indicator (fun r => a r z.1) z.2
  let H := fun z : Ω × ℝ => (Iic b).indicator (fun r => v r z.1) z.2
  have hX := finite_drift_semimartingale P F hF Z a b hb hZ0 hZc ha hac hM
  have hY := finite_drift_semimartingale P F hF V v b hb hV0 hVc hv hvc hN
  have hpm : Monotone p := fun s t hst => finite_prefix_time_mono b hb hst
  have hpc : Continuous p := continuous_subtype_val.comp (finite_prefix_time_continuous b hb)
  have hclock := (continuous_increasing_adapted_variation (by simp : (0:EReal)<⊤) F hF
    (fun (t : HalfClosedTime) (_ : Ω) => p t) (fun _ _ => measurable_const)
    (fun _ => hpm.monotoneOn _) (fun _ _ _ => hpc.continuousAt)).toPathwise
  apply density_product_bracket P F hF hle hnull X Y A B _ _ _ _ hX hY G H
    (fun w => (ham w).indicator measurableSet_Iic) (fun w => (hvm w).indicator measurableSet_Iic)
    (fun r hr w => clipped_driver_interval_integrable (fun u => a u w) b r hb hr
      (((hac w).intervalIntegrable_of_Icc (μ := volume) hb).1))
    (fun r hr w => clipped_driver_interval_integrable (fun u => v u w) b r hb hr
      (((hvc w).intervalIntegrable_of_Icc (μ := volume) hb).1))
  · intro r hr w
    dsimp [A,X,p,G]
    rw [finite_prefix_bot,frozen_drift_integral _ b r hb hr]
  · intro r hr w
    dsimp [B,Y,p,H]
    rw [finite_prefix_bot,frozen_drift_integral _ b r hb hr]
  · exact hQ
  · exact hclock.smul F c
  · intro t
    exact measurable_const
  · intro w
    exact continuous_const.mul hpc
  · intro r hr w
    change Z (p (realTimeClamp r)) w*V (p (realTimeClamp r)) w-Z 0 w*V 0 w-
      (∫ u in 0..p (realTimeClamp r),V u w*a u w+Z u w*v u w+c)=_
    have hpa : p (realTimeClamp r)∈Icc 0 b := (finitePrefixTime b hb (realTimeClamp r)).property
    have hi : IntervalIntegrable (fun u => V u w*a u w) volume 0 (p (realTimeClamp r)) :=
      (((hVc w).mul (hac w)).mono (Icc_subset_Icc le_rfl hpa.2)).intervalIntegrable_of_Icc hpa.1
    have hj : IntervalIntegrable (fun u => Z u w*v u w) volume 0 (p (realTimeClamp r)) :=
      (((hZc w).mul (hvc w)).mono (Icc_subset_Icc le_rfl hpa.2)).intervalIntegrable_of_Icc hpa.1
    rw [intervalIntegral.integral_add (hi.add hj) intervalIntegrable_const,
      intervalIntegral.integral_add hi hj,intervalIntegral.integral_const]
    dsimp only [X,Y,G,H,p]
    rw [finite_prefix_bot,frozen_weighted_drift_integral (fun u => a u w) (fun u => V u w) b r hb hr,
      frozen_weighted_drift_integral (fun u => v u w) (fun u => Z u w) b r hb hr,finite_prefix_time_min b r hb hr le_top]
    simp only [sub_zero,smul_eq_mul]
    ring
end Asakura.Chapter9
