import Chapter6BoundedVectorConstruction
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

/-- Actual finite-horizon Girsanov construction for bounded progressive vector
integrands: the density is proved to have mean one, and the changed Brownian
driver is constructed, with the prescribed integral drift on the horizon. -/
theorem bounded_progressive_girsanov
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {noise : ℕ} (B : BrownianSystem P noise)
    (H : Fin noise → Ω × ℝ → ℝ) (hHm : ∀ i,Measurable (H i))
    (hHp : ∀ i b,0 < b → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H i (z.1,z.2.val)))
    (K : ℝ) (hK : 0 ≤ K) (hHb : ∀ i z,|H i z| ≤ K)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ (Q : Measure Ω) (hQp : IsProbabilityMeasure Q),
      (∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w) ∧
      ∃ BQ : BrownianSystem Q noise,BQ.F = B.F ∧
        ∀ j r,0 ≤ r → BQ.W j (realTimeClamp r) =ᵐ[Q]
          fun w => B.W j (realTimeClamp r) w-∫ s in 0..min R r,H j (w,s) := by
  have hT : (0:EReal) < ⊤ := by simp
  obtain ⟨N,hN,hNI⟩ := bounded_vector_integrals_constructed P B H hHm hHp K hK hHb
  obtain ⟨hZ,C,L,hC,hL,hCe,hLe⟩ := bounded_vector_integral_covariances P B H hHm K hK hHb N hN hNI
  let Z := fun t w => ∑ i,N i t w
  let τ := fun _w : Ω => (realTimeClamp R : HalfClosedTime)
  have hτ t : MeasurableSet[B.F t] {w | τ w ≤ t} := by
    by_cases h : realTimeClamp R ≤ t <;> simp [τ,h]
  have hτt w : τ w < ⊤ := changed_time_finite R hR
  have hCm : Measurable[m] (C (realTimeClamp R)) :=
    ((covariance_adapted_variation P B.F B.mono B.le hZ hZ hC).adapted _ (changed_time_finite R hR)).mono (B.le _) le_rfl
  have hEi := exponential_integrable_of_upper_bound P _ hCm ((noise:ℝ)*K^2*R) 1 (by norm_num)
    (bounded_vector_clock_upper P H hHm K hK hHb C R hR (hCe R hR))
  obtain ⟨hMi,hMm,hmean,hbound⟩ := novikov_written P hT B.F B.mono B.le B.null Z C hZ hC
    τ hτ hτt 1 (by norm_num) hEi
  let D := fun w => Real.exp (Z (realTimeClamp R) w-C (realTimeClamp R) w/2)
  have hDi : Integrable D P := by simpa only [τ,min_top_right] using hMi ⊤
  have hDm : Measurable D := Real.continuous_exp.measurable.comp
    (((hZ.adapted P B.F _ (changed_time_finite R hR)).mono (B.le _) le_rfl).sub (hCm.div_const 2))
  have hmeanD : (∫ w,D w ∂P) = 1 := by simpa only [τ,min_top_right] using hmean
  let Q := P.withDensity (fun w => ENNReal.ofReal (D w))
  haveI hQp : IsProbabilityMeasure Q := mean_one_density_probability P D hDi
    (ae_of_all _ fun _ => (Real.exp_pos _).le) hmeanD
  have hAE := positive_real_density_ae_iff P Q D hDm (ae_of_all _ fun _ => Real.exp_pos _) rfl
  have hZs := hZ.stopped P B.F B.mono B.le τ hτ
  choose A hA using fun j => local_covariance_witness_exists P B.F B.mono B.le B.null
    (fun t w => Z (min (τ w) t) w) (B.W j) hZs (B.martingale j)
  obtain ⟨BQ,hBQ,hBWe⟩ := girsanov_brownian_vector_driver P Q B Z C hZ hC τ hτ hτt hmeanD rfl A hA
  refine ⟨Q,hQp,hAE,BQ,hBQ,?_⟩
  intro j r hr
  apply (hAE _).mp
  filter_upwards [local_covariance_one_sided_stopping P B.F B.mono B.le B.null Z (B.W j) (L j) (A j)
    hZ (B.martingale j) (hL j) τ hτ (hA j),hLe j (min R r) (le_min hR hr)] with w hw hl
  rw [hBWe,hw _ (changed_time_finite r hr)]
  have hmin : min (τ w) (realTimeClamp r) = realTimeClamp (min R r) :=
    (real_time_clamp_mono.map_min (a := R) (b := r)).symm
  rw [hmin,hl]

end Asakura.Chapter6
