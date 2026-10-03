import Chapter5TimeSpaceIntegrand
import Chapter5TimeDensityInitial

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Constructed time-space Ito with absolutely continuous drift and
quadratic variation. This is the stochastic energy identity's analytic
input, before the exponential-square function is substituted. -/
theorem time_space_drift_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M C : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hC : LocalCovarianceWitness P F M M C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (f : (Fin 2 → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (B : Ω × ℝ → ℝ) (hBm : ∀ w, Measurable (fun r => B (w,r)))
    (hBi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => B (w,r)) volume 0 (c n))
    (hAB : ∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), A (realTimeClamp r) w = A ⊥ w + ∫ s in 0..r, B (w,s))
    (G : Ω × ℝ → ℝ) (hGm : ∀ w, Measurable (fun r => G (w,r)))
    (hGi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)) volume 0 (c n))
    (hCG : ∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), C (realTimeClamp r) w = ∫ s in 0..r, G (w,s)) :
    let K := fun t => (finitePrefixTime (T := T) R hR t).val
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F M
        (fun z => fderiv ℝ f ![K (realTimeClamp z.2),X (realTimeClamp z.2) z.1] (Pi.single 1 1)) N ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ R →
        (fun w => f ![d,X (realTimeClamp d) w]) =ᵐ[P]
          fun w => f ![0,X ⊥ w] + N (realTimeClamp d) w +
            (∫ r in 0..d, fderiv ℝ f ![r,X (realTimeClamp r) w] (Pi.single 0 1)) +
            (∫ r in 0..d, fderiv ℝ f ![r,X (realTimeClamp r) w] (Pi.single 1 1)*B (w,r)) +
            (∫ r in 0..d, fderiv ℝ (fderiv ℝ f) ![r,X (realTimeClamp r) w]
              (Pi.single 1 1) (Pi.single 1 1)*G (w,r))/2 := by
  dsimp only
  obtain ⟨I,J,hI,hJ,he⟩ := time_space_ito_constructed P hT F hF hle hnull
    X A M C hX hC R hR hRT f hf c hc hcm hcT hcc
  obtain ⟨D,N,hDN,hD,hN⟩ := hI
  let K := fun t => (finitePrefixTime (T := T) R hR t).val
  let V := fun w r => ![K (realTimeClamp r),X (realTimeClamp r) w]
  let H := fun z : Ω × ℝ => fderiv ℝ (fderiv ℝ f) (V z.1 z.2) (Pi.single 1 1) (Pi.single 1 1)
  let H₁ := fun z : Ω × ℝ => fderiv ℝ f (V z.1 z.2) (Pi.single 1 1)
  obtain ⟨hHm,hHa,hHc⟩ := time_space_integrand_regularity P F X A M hX R hR
    (fun x => fderiv ℝ (fderiv ℝ f) x (Pi.single 1 1) (Pi.single 1 1))
    ((((hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const)
  obtain ⟨hH₁m,hH₁a,hH₁c⟩ := time_space_integrand_regularity P F X A M hX R hR
    (fun x => fderiv ℝ f x (Pi.single 1 1)) ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  refine ⟨N,hDN.martingale,hN,?_⟩
  intro d hd hdR
  have hdT : (d:EReal) < T := (EReal.coe_le_coe hdR).trans_lt hRT
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]; exact hdT
  have hjt := time_density_variation_integral P C J G H c hc hcT hcc hCG hGm hGi hHm (fun n => hHc (c n) (hc n) (hcT n)) hJ d hd hdT
  have hdt' := time_density_variation_integral_with_initial P A D (A ⊥) B H₁ c hc hcT hcc hAB hBm hBi
    hH₁m (fun n => hH₁c (c n) (hc n) (hcT n)) hD d hd hdT
  filter_upwards [he d hd hdR,hdt',hjt] with w hew hdw hjw
  rw [hDN.decomposition _ hdt w,hdw,hjw] at hew
  have hint : (∫ r in 0..d, H (w,r)*G (w,r)) =
      ∫ r in 0..d, fderiv ℝ (fderiv ℝ f) ![r,X (realTimeClamp r) w]
        (Pi.single 1 1) (Pi.single 1 1)*G (w,r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 d := by simpa [uIcc_of_le hd] using hr
    dsimp only [H,V,K]
    rw [finite_prefix_time_of_real R r hR (Icc_subset_Icc_right hdR hr') hRT.le]
  have hint₁ : (∫ r in 0..d, H₁ (w,r)*B (w,r)) =
      ∫ r in 0..d, fderiv ℝ f ![r,X (realTimeClamp r) w] (Pi.single 1 1)*B (w,r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 d := by simpa [uIcc_of_le hd] using hr
    dsimp only [H₁,V,K]
    rw [finite_prefix_time_of_real R r hR (Icc_subset_Icc_right hdR hr') hRT.le]
  rw [hint,hint₁] at hew
  linarith

end Asakura.Chapter5
