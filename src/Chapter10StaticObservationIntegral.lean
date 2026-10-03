import Chapter10StaticActualMean
import Chapter2VariationStoppedInterval

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Identify the actual integral of c/sigma² against the observation. This
connects the explicit static mean's Brownian representation to the manuscript's
observation-only formula. -/
theorem static_observation_integral {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (W C Y A Z : HalfClosedTime → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hZ : LocalMProcessWitness P F Z) (hCa : ∀ t,t<⊤ → Measurable[F t] (C t))
    (hclock : ∀ w r,0≤r → C (realTimeClamp r) w=r)
    (c : ℝ → ℝ) (hc : Continuous c) (σ : ℝ) (hσ : σ≠0) (V : Ω → ℝ)
    (hY : SemimartingaleDecomposition P F Y A (fun t w => σ*W t w))
    (hA : ∀ r,0≤r → ∀ w,A (realTimeClamp r) w=∫ s in 0..r,c s*V w)
    (hZI : ItoCovarianceFormula P F W (fun z => c z.2/σ) Z)
    (τ : ℕ → ℝ) (hτ : ∀ n,0≤τ n) (hτm : Monotone τ)
    (hτco : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := ⊤) (τ n)) :
    ∃ U,SemimartingaleIntegralFormula P F τ hτ A (fun t w => σ*W t w)
      (fun z => c z.2/σ^2) U ∧ ∀ t,0≤t → ∀ᵐ w ∂P,
        U (realTimeClamp t) w=(∫ s in 0..t,(c s)^2/σ^2)*V w+Z (realTimeClamp t) w := by
  have htop : (0:EReal)<⊤ := by simp
  obtain ⟨_,hCc⟩ := clock_regular_from_identity C (fun w r hr _ => hclock w r hr)
  obtain ⟨I,J,hIJ,hI,hJ⟩ := continuous_semimartingale_integral_exists P htop F hF hle hnull
    Y A (fun t w => σ*W t w) (fun t w => c (C t w)/σ^2) hY
    (fun t ht => (hc.measurable.comp (hCa t ht)).div_const _)
    (fun w t ht => (hc.continuousAt.comp (hCc w t ht)).div_const _)
    τ hτ hτm (fun n => EReal.coe_lt_top _) hτco
  have hI' := hI.congr_on_time_domain P τ hτ (fun n => EReal.coe_lt_top _) A I _
    (fun z => c z.2/σ^2) (fun w r hr _ => by rw [hclock w r hr])
  have hJ' := hJ.congr_on_time_domain P F _ J _ (fun z => c z.2/σ^2)
    (fun w r hr _ => by rw [hclock w r hr])
  have hZ' := hZI.congr_on_time_domain P F W Z _ (fun z => (c z.2/σ^2)*σ)
    (fun w r _ _ => by field_simp)
  have hJZ := ito_integral_associativity P htop F hF hle hnull W (fun t w => σ*W t w) J Z
    (fun _ => σ) (fun z => c z.2/σ^2) hW (hW.smul P F σ) hIJ.martingale hZ
    (fun _ => measurable_const) (fun _ => (hc.div_const _).measurable)
    (constant_ito_integral P htop F hF hle hnull W hW σ) hJ' hZ'
  refine ⟨(fun t w => I t w+J t w),⟨I,J,hIJ,hI',hJ'⟩,?_⟩
  intro t ht
  have hi := time_density_variation_integral_with_initial P A I (fun _ => 0) (fun z => c z.2*V z.1)
    (fun z => c z.2/σ^2) τ hτ (fun n => EReal.coe_lt_top _) hτco
    (fun n => ae_of_all _ fun w r hr => by simpa only [zero_add] using hA r hr.1 w)
    (fun w => by simpa only using! hc.measurable.mul_const (V w))
    (fun n => ae_of_all _ fun w => (hc.mul_const (V w)).intervalIntegrable 0 (τ n))
    (fun _ => (hc.div_const _).measurable) (fun _ _ => (hc.div_const _).continuousOn) hI' t ht (EReal.coe_lt_top t)
  filter_upwards [hi,hJZ] with w hi hj
  rw [hj _ (real_time_below t ht (EReal.coe_lt_top t)),hi]
  congr 1
  rw [←intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  ring

end Asakura.Chapter10
