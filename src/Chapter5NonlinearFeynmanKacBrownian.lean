import Chapter5NonlinearFeynmanKacDensity
import Chapter5BrownianIntegralBracket
import Chapter5BracketCommonTime
import Chapter5TimeSpaceIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Nonlinear Feynman--Kac with a general progressive diffusion coefficient.
The bracket and both composed stochastic integrals are constructed from
actual Ito covariance formulas, not postulated differential identities. -/
theorem nonlinear_feynman_kac_brownian
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (W A X M : ClosedTime T → Ω → ℝ) (U₀ : Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X (fun _ => U₀) M)
    (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (G : Ω × ℝ → ℝ) (hGm : ∀ w, Measurable (fun r => G (w,r)))
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (v : (Fin 2 → ℝ) → ℝ) (hv : ContDiff ℝ 2 v)
    (f : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hterminal : ∀ x, v ![R,x] = g x)
    (hpde : ∀ᵐ w ∂P,∀ r,r ∈ Icc 0 R →
      fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 0 1) +
      (fderiv ℝ (fderiv ℝ v) ![r,X (realTimeClamp r) w] (Pi.single 1 1) (Pi.single 1 1))*G (w,r)^2/2 +
      f r (v ![r,X (realTimeClamp r) w])
        (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r)) = 0)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hGi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hMG : ItoCovarianceFormula P F W G M) :
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W
        (fun z => fderiv ℝ v ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,
          X (realTimeClamp z.2) z.1] (Pi.single 1 1)*G z) N ∧
      ∀ t ∈ Icc 0 R,
        (fun w => g (X (realTimeClamp R) w)) =ᵐ[P]
          fun w => v ![t,X (realTimeClamp t) w] -
            (∫ r in t..R, f r (v ![r,X (realTimeClamp r) w])
              (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)*G (w,r))) +
            (N (realTimeClamp R) w - N (realTimeClamp t) w) := by
  obtain ⟨C,hC,hCG⟩ := clock_ito_integral_bracket P hT F hF hle hnull
    W A M hW hA hX.martingale c hc hcm hcT hct hcut hcc hclock G hG hGi hMG
  have hCGall n : ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), C (realTimeClamp r) w = ∫ s in 0..r, G (w,s)^2 := by
    refine bracket_primitive_common_time P (c n) (hc n).le (fun r => C (realTimeClamp r)) (fun w r => G (w,r)^2) ?_ (hGi n) ?_
    · intro w r hr
      have hrt : realTimeClamp (T := T) r < ⊤ := by
        change (realTimeClamp r : EReal) < T
        rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans (hcT n).le)]
        exact (EReal.coe_le_coe hr.2).trans_lt (hcT n)
      have hm := hX.martingale.path P F w _ hrt
      have hh := (hm.mul hm).sub (hC.defect.path P F w _ hrt)
      have hcp : ContinuousAt (fun t => C t w) (realTimeClamp r) := by
        convert hh using 1
        funext t
        dsimp only [Pi.sub_apply,Pi.mul_apply]
        ring
      exact (hcp.comp real_time_clamp_continuous.continuousAt).continuousWithinAt
    · intro r hr
      exact hCG r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))
  obtain ⟨N,hN,hNI,he⟩ := nonlinear_feynman_kac_density P hT F hF hle hnull
    X M C U₀ hX hC G hGm R hR hRT v hv f g hterminal hpde c (fun n => (hc n).le)
    hcm.monotone hcT hcc hGi hCGall
  let H := fun z : Ω × ℝ => fderiv ℝ v ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,
    X (realTimeClamp z.2) z.1] (Pi.single 1 1)
  obtain ⟨hHm,hHa,hHc⟩ := time_space_integrand_regularity P F X (fun _ => U₀) M hX R hR
    (fun x => fderiv ℝ v x (Pi.single 1 1)) ((hv.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hAm n w : MonotoneOn (fun r => A (realTimeClamp r) w) (Icc 0 (c n)) := by
    intro s hs t ht hst
    simpa only [hclock n w s hs,hclock n w t ht] using hst
  have hAc n w : ContinuousOn (fun r => A (realTimeClamp r) w) (Icc 0 (c n)) := by
    apply continuousOn_id.congr
    intro r hr; exact hclock n w r hr
  have hm n w : (intervalStieltjes 0 (c n) (hc n).le
      (fun r => A (realTimeClamp r) w) (hAm n w)
      (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure = volume.restrict (Ioc 0 (c n)) := by
    rw [← clock_stieltjes_measure 0 (c n) (hc n).le]
    congr 1
    apply StieltjesFunction.ext
    intro r
    exact hclock n w _ (intervalClamp_mem _ _ _ _)
  have his n : ∀ᵐ w ∂P, Integrable (fun r => G (w,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le
        (fun r => A (realTimeClamp r) w) (hAm n w)
        (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure := by
    filter_upwards [hGi n] with w hw
    rw [hm]
    exact hw.1
  obtain ⟨Z,hZ,hZI,hNZ⟩ := continuous_multiplier_ito_composition P hT F hF hle hnull
    W A M N hW hA hX.martingale hN c hc hcm hcT hct hcut hcc hAm hAc G H
    hGm hHm hG hHa (fun n => hHc (c n) (hc n).le (hcT n)) his hMG hNI
  refine ⟨Z,hZ,hZI,?_⟩
  intro t ht
  have hfinite (r : ℝ) (hr : r ∈ Icc 0 R) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hRT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hRT
  filter_upwards [he t ht,hNZ] with w hew hw
  rw [hw _ (hfinite R ⟨hR,le_rfl⟩),hw _ (hfinite t ht)] at hew
  exact hew

end Asakura.Chapter5
