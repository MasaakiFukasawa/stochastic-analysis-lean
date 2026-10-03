import Chapter2ItoConstructionIsometry
import Chapter3DoobSquareMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Construct the integral first, then apply Doob to its actual continuous
M2 extension. The approximating sums and their integrand-energy convergence
are retained in the conclusion to identify this as the integral of H.
This supplies the stochastic maximal estimate used in Picard/Euler; it does
not yet identify Brownian Stieltjes energy with the time integral. -/
theorem constructed_ito_maximal_estimate
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure)
    (CT : Ω → ℝ) (hCT : Integrable CT P)
    (hCTlim : ∀ᵐ ω ∂P, Tendsto (fun n => ∫ r, H (ω,r)^2
      ∂(intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure) atTop (𝓝 (CT ω))) :
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → ℝ) (V : ℕ → ℕ → Ω → ℝ)
      (Z : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ)) (Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ)),
      (∀ n, StrictMonoOn (u n) (Iic (N n))) ∧
      (∀ n i, i ≤ N n → u n i ∈ Icc 0 (c n)) ∧
      (∀ n i, i < N n → Measurable[F (realTimeClamp (u n i))] (V n i) ∧ MemLp (V n i) ∞ P) ∧
      (∀ n ω t, Z n ω t = ∑ i ∈ Finset.range (N n), V n i ω*
        stepIncrement (realTimeClamp (u n i)) (realTimeClamp (u n (i+1))) (fun s => X s ω) t.val) ∧
      LocalMProcessWitness P F (fun t ω => extendOpenPath (Y ω) t) ∧
      Tendsto (fun n => ∫ ω, pathDistance (intervalTimeExhaustion (fun n => realTimeClamp (c n)) hct hcut hcc)
        (Z n ω) (Y ω) ∂P) atTop (𝓝 0) ∧
      ∃ Ybar : ClosedTime T → Ω → ℝ, ∃ hYbar : ContinuousM2Witness P F Ybar,
      ((∀ t, t < ⊤ → Ybar t =ᵐ[P] (fun ω => extendOpenPath (Y ω) t)) ∧
        Tendsto (fun n => eLpNorm ((fun ω => extendOpenPath (Y ω) (realTimeClamp (c n)))-Ybar ⊤) 2 P) atTop (𝓝 0) ∧
        Tendsto (fun t => eLpNorm ((fun ω => extendOpenPath (Y ω) t)-Ybar ⊤) 2 P) (𝓝[<] (⊤ : ClosedTime T)) (𝓝 0) ∧
        ‖(hYbar.moment ⊤).toLp (Ybar ⊤)‖^2 = ∫ ω, CT ω ∂P) ∧
      ∃ B : ClosedTime T → Ω → ℝ,
      LocalCovarianceWitness P F (fun t ω => extendOpenPath (Y ω) t)
        (fun t ω => extendOpenPath (Y ω) t) B ∧
      (∀ j, B (realTimeClamp (c j)) =ᵐ[P] fun ω => ∫ r, H (ω,r)^2
        ∂(intervalStieltjes 0 (c j) (hc j).le (fun r => A (realTimeClamp r) ω) (hAm j ω)
          (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure) ∧
      (∀ j (ε : ℝ), 0 < ε → Tendsto (fun n => P {ω | ε ≤ ∫ r,
        ((∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r)-H (ω,r))^2
        ∂(intervalStieltjes 0 (c j) (hc j).le (fun r => A (realTimeClamp r) ω) (hAm j ω)
          (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0)) ∧
      Integrable (fun ω => ‖continuousPath Ybar hYbar.path ω‖^2) P ∧
      (∫ ω, ‖continuousPath Ybar hYbar.path ω‖^2 ∂P) ≤ 4*(∫ ω, CT ω ∂P) := by
  obtain ⟨N,u,V,Z,Y,hu,hub,hVm,hZ,hY,hlim,Ybar,hYbar,hterminal,B,hB,henergy,hprob⟩ :=
    ito_integral_constructed_with_terminal_isometry P hT F hF hle hnull X A hX hA
      c hc hcm hcT hct hcut hcc hAm hAc H hH hi CT hCT hCTlim
  have hmax := continuous_m2_path_square_moment P F hF hle Ybar hYbar
  have hiso := hterminal.2.2.2
  rw [norm_toLp_square_integral] at hiso
  refine ⟨N,u,V,Z,Y,hu,hub,hVm,hZ,hY,hlim,Ybar,hYbar,hterminal,B,hB,henergy,hprob,hmax.1,?_⟩
  simpa only [hiso] using hmax.2

end Asakura.Chapter4
