import Chapter10DensityProductIntegrals
import Chapter10ScaledIntegrator
import Chapter8BrownianForcingPath

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The Kyle profit identity is derived from the actual square formula.
Orders need only pathwise local absolute integrability, not continuity or a
finite integral of their squares. -/
theorem kyle_ito_profit_identity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (B C E A : HalfClosedTime → Ω → ℝ) (V : Ω → ℝ) (p0 l σ : ℝ) (hl : 0<l)
    (α : Ω × ℝ → ℝ) (hαm : ∀ w,Measurable (fun s => α (w,s)))
    (hαi : ∀ t,0≤t → ∀ w,IntervalIntegrable (fun s => α (w,s)) volume 0 t)
    (hB : LocalMProcessWitness P F B) (hC : LocalCovarianceWitness P F B B C)
    (hclock : ∀ t,0≤t → ∀ w,C (realTimeClamp t) w=t)
    (hE : SemimartingaleDecomposition P F E A (fun t w => (-l*σ)*B t w))
    (hA : ∀ t,0≤t → ∀ w,A (realTimeClamp t) w=V w-p0-l*(∫ s in 0..t,α (w,s))) :
    ∃ Z : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F B (fun z => E (realTimeClamp z.2) z.1) Z ∧
      ∀ t,0≤t → ∀ᵐ w ∂P,
        (∫ s in 0..t,E (realTimeClamp s) w*α (w,s))=
          ((V w-p0)^2-(E (realTimeClamp t) w)^2)/(2*l)+l*σ^2*t/2-σ*Z (realTimeClamp t) w := by
  have hEa (t : HalfClosedTime) (ht : t<⊤) : Measurable[F t] (E t) := by
    rw [show E t=(fun w => A t w+(-l*σ)*B t w) from funext (hE.decomposition t ht)]
    exact (hE.variation.adapted t ht).add ((hB.adapted P F t ht).const_mul _)
  have hEr w : Continuous (fun s : ℝ => E (realTimeClamp s) w) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hE.continuous w _ (half_real_time_finite s)).comp real_time_clamp_continuous.continuousAt
  obtain ⟨Z,hZ,hZI⟩ := continuous_adapted_ito_exists P (by simp : (0:EReal)<⊤) F hF hle hnull B hB
    (fun z => E (realTimeClamp z.2) z.1)
    (fun s hs hsT => hEa _ (real_time_below s hs hsT))
    (fun _ _ _ w => (hEr w).continuousOn)
  have hscaledC : LocalCovarianceWitness P F (fun t w => (-l*σ)*B t w)
      (fun t w => (-l*σ)*B t w) (fun t w => (-l*σ)^2*C t w) := by
    refine ⟨?_,hC.variation.smul F ((-l*σ)^2)⟩
    convert hC.defect.smul P F ((-l*σ)^2) using 1
    funext t w
    ring
  have hAd (t : ℝ) (ht : 0≤t) w : A (realTimeClamp t) w=(V w-p0)+∫ s in 0..t,(-l)*α (w,s) := by
    rw [hA t ht w,intervalIntegral.integral_const_mul]
    ring
  obtain ⟨J,L,hJ,hL,hJI,hLI,hprod⟩ := density_product_with_integrals P F hF hle hnull E E A A
    (fun t w => (-l*σ)*B t w) (fun t w => (-l*σ)*B t w) (fun t w => (-l*σ)^2*C t w)
    hE hE hscaledC (fun w => V w-p0) (fun w => V w-p0)
    (fun z => (-l)*α z) (fun z => (-l)*α z)
    (fun w => (hαm w).const_mul _) (fun w => (hαm w).const_mul _)
    (fun t ht w => (hαi t ht w).const_mul _) (fun t ht w => (hαi t ht w).const_mul _) hAd hAd
  have hJZ := scaled_integrator_identity P (by simp : (0:EReal)<⊤) F hF hle hnull B J Z
    (fun z => E (realTimeClamp z.2) z.1) (-l*σ) hB hJ hZ (fun w => (hEr w).measurable) hJI hZI
  have hLZ := scaled_integrator_identity P (by simp : (0:EReal)<⊤) F hF hle hnull B L Z
    (fun z => E (realTimeClamp z.2) z.1) (-l*σ) hB hL hZ (fun w => (hEr w).measurable) hLI hZI
  have hzero : realTimeClamp (T := (⊤:EReal)) 0=⊥ := Subtype.ext (real_time_clamp_eq 0 le_rfl le_top)
  have hE0 : E ⊥=ᵐ[P] (fun w => V w-p0) := by
    filter_upwards [hB.initial P F] with w hw
    have hh := hE.decomposition ⊥ (by change (0:EReal)<⊤; simp) w
    have ha := hA 0 le_rfl w
    simp only [hzero,intervalIntegral.integral_same,mul_zero,sub_zero] at ha
    simpa only [ha,hw,Pi.zero_apply,mul_zero,add_zero] using hh
  refine ⟨Z,hZ,hZI,?_⟩
  intro t ht
  filter_upwards [hprod t ht,hJZ,hLZ,hE0] with w hp hj hlz he0
  have htfin := half_real_time_finite t
  rw [hj _ htfin,hlz _ htfin,he0,hclock t ht w] at hp
  have hid : (∫ s in 0..t,E (realTimeClamp s) w*((-l)*α (w,s)))=
      (-l)*(∫ s in 0..t,E (realTimeClamp s) w*α (w,s)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [hid] at hp
  field_simp [hl.ne']
  nlinarith [hp]

end Asakura.Chapter10
