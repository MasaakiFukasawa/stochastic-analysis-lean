import Chapter5TimeSpaceIto
import Chapter5TimeDensityVariation
import Chapter5FrozenCoordinates
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Time-space Ito for a martingale with a random initial value and an
absolutely continuous bracket. Both integrals are constructed from the
previous chapters; the second-order term is an ordinary time integral. -/
theorem time_space_density_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X M C : ClosedTime T → Ω → ℝ) (U : Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X (fun _ => U) M)
    (hC : LocalCovarianceWitness P F M M C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (f : (Fin 2 → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
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
            (∫ r in 0..d, fderiv ℝ (fderiv ℝ f) ![r,X (realTimeClamp r) w]
              (Pi.single 1 1) (Pi.single 1 1)*G (w,r))/2 := by
  dsimp only
  obtain ⟨I,J,hI,hJ,he⟩ := time_space_ito_constructed P hT F hF hle hnull
    X (fun _ => U) M C hX hC R hR hRT f hf c hc hcm hcT hcc
  obtain ⟨D,N,hDN,hD,hN⟩ := hI
  have hd : VariationIntegralFormula P c hc (fun _ _ => 0) _ D :=
    variation_integral_integrator_increments_congr P (fun _ => U) (fun _ _ => 0) D _ c hc hcT hD
      (ae_of_all _ fun _ _ _ _ _ => by simp)
  have hd0 := hd.unique P c hc hcc _ D (fun _ _ => 0) _ (zero_variation_integral P c hc _)
  let K := fun t => (finitePrefixTime (T := T) R hR t).val
  let V := fun w r => ![K (realTimeClamp r),X (realTimeClamp r) w]
  let H := fun z : Ω × ℝ => fderiv ℝ (fderiv ℝ f) (V z.1 z.2) (Pi.single 1 1) (Pi.single 1 1)
  have hDc : Continuous (fun x => fderiv ℝ (fderiv ℝ f) x (Pi.single 1 1) (Pi.single 1 1)) :=
    (((hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const
  have hK : Continuous K := continuous_subtype_val.comp (finite_prefix_time_continuous R hR)
  have hHm w : Measurable (fun r => H (w,r)) := by
    apply hDc.measurable.comp
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact hK.measurable.comp real_time_clamp_continuous.measurable
    · exact open_path_real_measurable _ (hX.continuous w)
  have hHc n w : ContinuousOn (fun r => H (w,r)) (Icc 0 (c n)) := by
    apply hDc.comp_continuousOn
    intro r hr
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact hK.continuousAt.comp real_time_clamp_continuous.continuousAt
    · have hrt : realTimeClamp (T := T) r < ⊤ := by
        change (realTimeClamp r : EReal) < T
        rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans (hcT n).le)]
        exact (EReal.coe_le_coe hr.2).trans_lt (hcT n)
      exact (hX.continuous w _ hrt).comp real_time_clamp_continuous.continuousAt
  refine ⟨N,hDN.martingale,hN,?_⟩
  intro d hd hdR
  have hdT : (d:EReal) < T := (EReal.coe_le_coe hdR).trans_lt hRT
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]; exact hdT
  have hjt := time_density_variation_integral P C J G H c hc hcT hcc hCG hGm hGi hHm hHc hJ d hd hdT
  filter_upwards [he d hd hdR,hd0,hjt] with w hew hdw hjw
  rw [hDN.decomposition _ hdt w,hdw _ hdt,zero_add,hjw] at hew
  have hint : (∫ r in 0..d, H (w,r)*G (w,r)) =
      ∫ r in 0..d, fderiv ℝ (fderiv ℝ f) ![r,X (realTimeClamp r) w]
        (Pi.single 1 1) (Pi.single 1 1)*G (w,r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 d := by simpa [uIcc_of_le hd] using hr
    dsimp only [H,V,K]
    rw [finite_prefix_time_of_real R r hR (Icc_subset_Icc_right hdR hr') hRT.le]
  rw [hint] at hew
  linarith

end Asakura.Chapter5
