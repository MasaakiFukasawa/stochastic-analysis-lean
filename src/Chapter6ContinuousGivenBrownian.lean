import Chapter6ContinuousVectorCovariance
import Chapter6BoundedClockExponential
import Chapter6GirsanovBrownian
import Chapter6DensityProbability
import Chapter2OneSidedStoppedCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Given the proved mean-one density of a continuous integrand, construct
the changed Brownian driver with its actual integral drift. Boundedness
of the integrand is not assumed here. -/
theorem continuous_given_density_brownian
    {Ω : Type*} {m : MeasurableSpace Ω} (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {noise : ℕ} (B : BrownianSystem P noise)
    (H : Fin noise → Ω × ℝ → ℝ) (hHm : ∀ i,Measurable (H i))
    (hHc : ∀ j w,Continuous (fun r => H j (w,r)))
    (N : Fin noise → HalfClosedTime → Ω → ℝ) (hN : ∀ j,LocalMProcessWitness P B.F (N j))
    (hNI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (H j) (N j))
    (C : HalfClosedTime → Ω → ℝ)
    (hC : LocalCovarianceWitness P B.F (fun t w => ∑ j,N j t w) (fun t w => ∑ j,N j t w) C)
    (R : ℝ) (hR : 0≤R)
    (hmeanD : (∫ w,Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2) ∂P)=1)
    (hQD : Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2)))) :
      ∃ BQ : BrownianSystem Q noise,BQ.F = B.F ∧
        ∀ j r,0 ≤ r → BQ.W j (realTimeClamp r) =ᵐ[Q]
          fun w => B.W j (realTimeClamp r) w-∫ s in 0..min R r,H j (w,s) := by
  have hT : (0:EReal) < ⊤ := by simp
  obtain ⟨hZ,C',L,hC',hL,hCe,hLe⟩ := continuous_vector_integral_covariances P B H hHm hHc N hN hNI
  let Z := fun t w => ∑ i,N i t w
  let τ := fun _w : Ω => (realTimeClamp R : HalfClosedTime)
  have hτ t : MeasurableSet[B.F t] {w | τ w ≤ t} := by
    by_cases h : realTimeClamp R ≤ t <;> simp [τ,h]
  have hτt w : τ w < ⊤ := changed_time_finite R hR
  have hCm : Measurable[m] (C (realTimeClamp R)) :=
    ((covariance_adapted_variation P B.F B.mono B.le hZ hZ hC).adapted _ (changed_time_finite R hR)).mono (B.le _) le_rfl
  let D := fun w => Real.exp (Z (realTimeClamp R) w-C (realTimeClamp R) w/2)
  have hDm : Measurable D := Real.continuous_exp.measurable.comp
    (((hZ.adapted P B.F _ (changed_time_finite R hR)).mono (B.le _) le_rfl).sub (hCm.div_const 2))
  have hAE := positive_real_density_ae_iff P Q D hDm (ae_of_all _ fun _ => Real.exp_pos _) hQD
  have hZs := hZ.stopped P B.F B.mono B.le τ hτ
  choose A hA using fun j => local_covariance_witness_exists P B.F B.mono B.le B.null
    (fun t w => Z (min (τ w) t) w) (B.W j) hZs (B.martingale j)
  obtain ⟨BQ,hBQ,hBWe⟩ := girsanov_brownian_vector_driver P Q B Z C hZ hC τ hτ hτt hmeanD hQD A hA
  refine ⟨BQ,hBQ,?_⟩
  intro j r hr
  apply (hAE _).mp
  filter_upwards [local_covariance_one_sided_stopping P B.F B.mono B.le B.null Z (B.W j) (L j) (A j)
    hZ (B.martingale j) (hL j) τ hτ (hA j),hLe j (min R r) (le_min hR hr)] with w hw hl
  rw [hBWe,hw _ (changed_time_finite r hr)]
  have hmin : min (τ w) (realTimeClamp r) = realTimeClamp (min R r) :=
    (real_time_clamp_mono.map_min (a := R) (b := r)).symm
  rw [hmin,hl]

end Asakura.Chapter6
