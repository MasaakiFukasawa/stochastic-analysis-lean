import Chapter6GirsanovWritten
import Chapter6DriftCrossCovariance
import Chapter6PositiveRealDensity
import Chapter4BrownianSystem

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The corrected driver is Brownian under the density measure, with its
actual quadratic variation proved by the common-path partition argument. -/
theorem girsanov_brownian_driver
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1)
    (Z C : HalfClosedTime → Ω → ℝ) (hZ : LocalMProcessWitness P B.F Z)
    (hC : LocalCovarianceWitness P B.F Z Z C)
    (τ : Ω → HalfClosedTime) (hτ : ∀ t,MeasurableSet[B.F t] {w | τ w ≤ t})
    (hτt : ∀ w,τ w < ⊤)
    (hmean : (∫ w,Real.exp (Z (τ w) w-C (τ w) w/2) ∂P) = 1)
    (hQ : Q = P.withDensity (fun w => ENNReal.ofReal (Real.exp (Z (τ w) w-C (τ w) w/2))))
    (K : HalfClosedTime → Ω → ℝ)
    (hK : LocalCovarianceWitness P B.F (fun t w => Z (min (τ w) t) w) (B.W 0) K) :
    ∃ BQ : BrownianSystem Q 1,BQ.F = B.F ∧
      (∀ t w,BQ.W 0 t w = B.W 0 t w-K t w) := by
  have hT : (0:EReal) < ⊤ := by simp
  let D := fun w => Real.exp (Z (τ w) w-C (τ w) w/2)
  obtain ⟨hMa,_,_,_,_⟩ := stochastic_exponential_closed_martingale P hT B.F B.mono B.le B.null
    Z C hZ hC τ hτ hτt hmean
  have hDm : Measurable[m] D := by
    simpa only [min_top_right] using (hMa ⊤).mono (B.le ⊤) le_rfl
  have hAE := fun p => positive_real_density_ae_iff P Q D hDm (ae_of_all _ fun _ => Real.exp_pos _) hQ p
  have hnullQ := null_sets_transfer_to_equivalent_measure P Q B.F B.null hAE
  have hV := girsanov_maruyama_written P Q hT B.F B.mono B.le B.null Z C hZ hC τ hτ hτt
    hmean hQ (B.W 0) K (B.martingale 0) hK
  have hZ' := hZ.stopped P B.F B.mono B.le τ hτ
  have hKv := covariance_adapted_variation P B.F B.mono B.le hZ' (B.martingale 0) hK
  have hKc := local_covariance_path_continuous P B.F _ _ K hZ' (B.martingale 0) hK
  have hVC := drift_corrected_quadratic_variation P Q hT B.F B.mono B.le B.null hnullQ hAE
    (B.W 0) K (B.C 0 0) (B.martingale 0) (B.cov 0 0) hKv hKc hV
  refine ⟨{
    F := B.F
    mono := B.mono
    le := B.le
    null := hnullQ
    W := fun _ t w => B.W 0 t w-K t w
    C := fun _ _ => B.C 0 0
    martingale := fun _ => hV
    cov := fun _ _ => hVC
    clock := ?_ },rfl,fun _ _ => rfl⟩
  intro j k w r hr
  simp only [Subsingleton.elim j k,ite_true]
  exact B.diagonal_clock 0 w r hr

theorem girsanov_brownian_vector_driver
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {noise : ℕ} (B : BrownianSystem P noise)
    (Z C : HalfClosedTime → Ω → ℝ) (hZ : LocalMProcessWitness P B.F Z)
    (hC : LocalCovarianceWitness P B.F Z Z C)
    (τ : Ω → HalfClosedTime) (hτ : ∀ t,MeasurableSet[B.F t] {w | τ w ≤ t})
    (hτt : ∀ w,τ w < ⊤)
    (hmean : (∫ w,Real.exp (Z (τ w) w-C (τ w) w/2) ∂P) = 1)
    (hQ : Q = P.withDensity (fun w => ENNReal.ofReal (Real.exp (Z (τ w) w-C (τ w) w/2))))
    (K : Fin noise → HalfClosedTime → Ω → ℝ)
    (hK : ∀ j,LocalCovarianceWitness P B.F (fun t w => Z (min (τ w) t) w) (B.W j) (K j)) :
    ∃ BQ : BrownianSystem Q noise,BQ.F = B.F ∧
      (∀ j t w,BQ.W j t w = B.W j t w-K j t w) := by
  have hT : (0:EReal) < ⊤ := by simp
  let D := fun w => Real.exp (Z (τ w) w-C (τ w) w/2)
  obtain ⟨hMa,_,_,_,_⟩ := stochastic_exponential_closed_martingale P hT B.F B.mono B.le B.null
    Z C hZ hC τ hτ hτt hmean
  have hDm : Measurable[m] D := by
    simpa only [min_top_right] using (hMa ⊤).mono (B.le ⊤) le_rfl
  have hAE := fun p => positive_real_density_ae_iff P Q D hDm (ae_of_all _ fun _ => Real.exp_pos _) hQ p
  have hnullQ := null_sets_transfer_to_equivalent_measure P Q B.F B.null hAE
  have hV j := girsanov_maruyama_written P Q hT B.F B.mono B.le B.null Z C hZ hC τ hτ hτt
    hmean hQ (B.W j) (K j) (B.martingale j) (hK j)
  have hZ' := hZ.stopped P B.F B.mono B.le τ hτ
  have hKv j := covariance_adapted_variation P B.F B.mono B.le hZ' (B.martingale j) (hK j)
  have hKc j := local_covariance_path_continuous P B.F _ _ (K j) hZ' (B.martingale j) (hK j)
  have hVC j k := drift_corrected_cross_covariance P Q hT B.F B.mono B.le B.null hnullQ hAE
    (B.W j) (B.W k) (K j) (K k) (B.C j j) (B.C k k) (B.C j k)
    (B.martingale j) (B.martingale k) (B.cov j j) (B.cov k k) (B.cov j k)
    (hKv j) (hKv k) (hKc j) (hKc k) (hV j) (hV k)
  refine ⟨{
    F := B.F
    mono := B.mono
    le := B.le
    null := hnullQ
    W := fun j t w => B.W j t w-K j t w
    C := B.C
    martingale := hV
    cov := hVC
    clock := B.clock },rfl,fun _ _ _ => rfl⟩

end Asakura.Chapter6
