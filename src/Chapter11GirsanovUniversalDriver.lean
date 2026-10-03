import Chapter11MeasureChangedIntegral
import Chapter11BrownianIntegralCovariances
import Chapter11BrownianLocalIntegral
import Chapter6GirsanovItoDrift
import Chapter6GirsanovBrownian

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the changed Brownian driver and identify the integral of an
 arbitrary locally square integrable integrand under the two measures.
 The correction is obtained from covariation, not assumed as an identity. -/
theorem girsanov_driver_all_integrands {Ω : Type*} [m : MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (β : Ω × ℝ → ℝ)
    (hβm : Measurable β)
    (k : ℝ) (hβb : ∀ z,|β z|≤k)
    (Z C : HalfClosedTime → Ω → ℝ)
    (hZ : LocalMProcessWitness P B.F Z)
    (hZI : ItoCovarianceFormula P B.F (B.W 0) β Z)
    (hC : LocalCovarianceWitness P B.F Z Z C)
    (R : ℝ) (hR : 0≤R)
    (hmean : (∫ w,Real.exp (Z (realTimeClamp R) w-C (realTimeClamp R) w/2) ∂P)=1)
    (hQ : Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp (Z (realTimeClamp R) w-C (realTimeClamp R) w/2)))) :
    ∃ BQ : BrownianSystem Q 1,BQ.F=B.F ∧
      ∀ (H : Ω × ℝ → ℝ),Measurable H →
      (∀ d : ℝ,0<d → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val))) →
      (∀ d : ℝ,0≤d → ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 d) →
      ∀ X : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F X →
      ItoCovarianceFormula P B.F (B.W 0) H X →
      ∃ N L : HalfClosedTime → Ω → ℝ,
        LocalMProcessWitness Q BQ.F N ∧ ItoCovarianceFormula Q BQ.F (BQ.W 0) H N ∧
        (∀ᵐ w ∂P,∀ t,t<⊤ → X t w=N t w+L t w) ∧
        (∀ d : ℝ,0≤d → L (realTimeClamp d)=ᵐ[P] fun w => ∫ s in 0..min R d,β (w,s)*H (w,s)) := by
  let τ := fun _w : Ω => (realTimeClamp R : HalfClosedTime)
  have hτ t : MeasurableSet[B.F t] {w | τ w≤t} := by
    by_cases h : realTimeClamp R≤t <;> simp [τ,h]
  have hτt w : τ w<⊤ := changed_time_finite R hR
  have hZs := hZ.stopped P B.F B.mono B.le τ hτ
  obtain ⟨K,hK⟩ := local_covariance_witness_exists P B.F B.mono B.le B.null
    (fun t w => Z (min (τ w) t) w) (B.W 0) hZs (B.martingale 0)
  obtain ⟨BQ,hF,hW⟩ := girsanov_brownian_driver P Q B Z C hZ hC τ hτ hτt hmean hQ K hK
  refine ⟨BQ,hF,?_⟩
  intro H hHm hHp hH2 X hX hXI
  have hDm : Measurable (fun w => Real.exp (Z (realTimeClamp R) w-C (realTimeClamp R) w/2)) :=
    ((hZ.adapted P B.F _ (changed_time_finite R hR)).mono (B.le _) le_rfl).sub
      ((((covariance_adapted_variation P B.F B.mono B.le hZ hZ hC).adapted _ (changed_time_finite R hR)).mono (B.le _) le_rfl).div_const 2) |>.exp
  have hAE := fun p => positive_real_density_ae_iff P Q _ hDm (ae_of_all _ fun _ => Real.exp_pos _) hQ p
  have hnullQ := null_sets_transfer_to_equivalent_measure P Q B.F B.null hAE
  obtain ⟨L,hLv,hLc,hLQ,hLe⟩ := girsanov_ito_drift P Q B β H hβm hHm k hβb Z X C hZ hX hZI hXI hC hH2 R hR hmean hQ
  have hHpQ : ∀ r : ℝ,0<r → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) r => BQ.F (realTimeClamp t.val))) inferInstance (fun z : Ω × Icc (0:ℝ) r => H (z.1,z.2.val)) := by
    rw [hF]; exact hHp
  obtain ⟨N,hN,hNI⟩ := brownian_local_integral Q BQ H hHm hHpQ (fun r hr => (hAE _).mp (hH2 r hr))
  obtain ⟨A,D,hA,hD,hAe,hDe⟩ := brownian_integral_covariances P B H hHm X hX hXI hH2
  obtain ⟨E,_,hE,_,hEe,_⟩ := brownian_integral_covariances Q BQ H hHm N hN hNI (fun r hr => (hAE _).mp (hH2 r hr))
  have hWfun : BQ.W 0=fun t w => B.W 0 t w-K t w := funext fun t => funext (hW t)
  have hWQ := BQ.martingale 0
  rw [hF,hWfun] at hWQ
  have hNI' := hNI
  rw [hF,hWfun] at hNI'
  have hN' := hN
  rw [hF] at hN' hE
  have he := measure_changed_integral_identified P Q B.F B.mono B.le B.null hnullQ hAE
    (B.W 0) X K L (B.C 0 0) A D N E (B.martingale 0) hX (B.cov 0 0) hA hD
    (covariance_adapted_variation P B.F B.mono B.le hZs (B.martingale 0) hK) hLv
    (local_covariance_path_continuous P B.F _ _ K hZs (B.martingale 0) hK) hLc
    hWQ hLQ hN' hE H (fun w => hHm.comp measurable_prodMk_left) hNI' hH2 hAe hDe hEe
  exact ⟨N,L,hN,hNI,he.2,hLe⟩

end Asakura.Chapter11
