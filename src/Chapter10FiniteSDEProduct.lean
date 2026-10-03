import Chapter10DensityProductFormula
import Chapter9FrozenDriftIntegrals

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter9
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The finite-horizon SDE product identity, with the two drift integrals
and the covariance density identified explicitly. -/
theorem finite_sde_product {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y a b : ℝ → Ω → ℝ) (ξ η : Ω → ℝ) (T : ℝ) (hT : 0≤T)
    (M N C : HalfClosedTime → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F
      (fun t w => X (finitePrefixTime T hT t).val w)
      (fun t w => ξ w+∫ s in 0..(finitePrefixTime T hT t).val,a s w) M)
    (hY : SemimartingaleDecomposition P F
      (fun t w => Y (finitePrefixTime T hT t).val w)
      (fun t w => η w+∫ s in 0..(finitePrefixTime T hT t).val,b s w) N)
    (hC : LocalCovarianceWitness P F M N C)
    (ha : ∀ w,Continuous (fun s => a s w)) (hb : ∀ w,Continuous (fun s => b s w))
    (q : ℝ → ℝ)
    (hcov : ∀ r∈Icc 0 T,C (realTimeClamp r) =ᵐ[P] fun _ => ∫ s in 0..r,q s) :
    ∃ Z : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P F Z ∧
      ∀ r∈Icc 0 T,∀ᵐ w ∂P,
        X r w*Y r w=X 0 w*Y 0 w+(∫ s in 0..r,Y s w*a s w)+
          (∫ s in 0..r,X s w*b s w)+(∫ s in 0..r,q s)+Z (realTimeClamp r) w := by
  let G := fun z : Ω × ℝ => (Iic T).indicator (fun s => a s z.1) z.2
  let H := fun z : Ω × ℝ => (Iic T).indicator (fun s => b s z.1) z.2
  have hGi r (hr : 0≤r) w : IntervalIntegrable (fun s => G (w,s)) volume 0 r := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr
    exact ((ha w).intervalIntegrable 0 r).1.indicator measurableSet_Iic
  have hHi r (hr : 0≤r) w : IntervalIntegrable (fun s => H (w,s)) volume 0 r := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr
    exact ((hb w).intervalIntegrable 0 r).1.indicator measurableSet_Iic
  obtain ⟨Z,hZ,he⟩ := density_product_local_martingale P F hF hle hnull _ _ _ _ M N C hX hY hC ξ η G H
    (fun w => (ha w).measurable.indicator measurableSet_Iic)
    (fun w => (hb w).measurable.indicator measurableSet_Iic) hGi hHi
    (by intro r hr w; rw [frozen_drift_integral (fun s => a s w) T r hT hr])
    (by intro r hr w; rw [frozen_drift_integral (fun s => b s w) T r hT hr])
  refine ⟨Z,hZ,?_⟩
  intro r hr
  filter_upwards [he r hr.1,hcov r hr] with w hw hcw
  have hp : (finitePrefixTime (T := (⊤:EReal)) T hT (realTimeClamp r)).val=r := by
    rw [finite_prefix_time_min T r hT hr.1 le_top,min_eq_left hr.2]
  simp only [G,H,finite_prefix_bot,hp,hcw] at hw
  rw [frozen_weighted_drift_integral (fun s => a s w) (fun s => Y s w) T r hT hr.1,
    frozen_weighted_drift_integral (fun s => b s w) (fun s => X s w) T r hT hr.1,
    min_eq_left hr.2] at hw
  exact hw

end Asakura.Chapter10
