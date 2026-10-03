import Chapter2ItoConstructionEnergy
import Chapter2IntegrableTerminalVariation
import Chapter2M2TimeContinuity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Full construction from a progressive integrand through elementary density,
local martingale completion, actual energy identification and an L2 terminal
limit. In particular no value of H dot X at T occurs in the assumptions. -/
theorem ito_integral_constructed_with_terminal_isometry
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
      ∀ j (ε : ℝ), 0 < ε → Tendsto (fun n => P {ω | ε ≤ ∫ r,
        ((∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r)-H (ω,r))^2
        ∂(intervalStieltjes 0 (c j) (hc j).le (fun r => A (realTimeClamp r) ω) (hAm j ω)
          (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0) := by
  obtain ⟨N,u,V,Z,Y,hu,hub,hVm,hZ,hY,hlim,B,hB,henergy,hprob⟩ :=
    ito_integral_constructed_with_energy P hT F hF hle hnull X A hX hA c hc hcm hcT
      hct hcut hcc hAm hAc H hH hi
  have hBlim : ∀ᵐ ω ∂P, Tendsto (fun n => B (realTimeClamp (c n)) ω) atTop (𝓝 (CT ω)) := by
    filter_upwards [ae_all_iff.2 henergy,hCTlim] with ω he hl
    simpa only [he] using hl
  have hBound n : ∀ᵐ ω ∂P, B (realTimeClamp (c n)) ω ≤ CT ω := by
    filter_upwards [hBlim,local_quadratic_variation_monotone P F hF hle hnull
      (fun t ω => extendOpenPath (Y ω) t) B hY hB] with ω hl hm
    apply ge_of_tendsto hl
    refine eventually_atTop.2 ⟨n,fun k hk => ?_⟩
    exact hm (hcut n) (hcut k) (hct.monotone hk)
  obtain ⟨Ybar,hYbar,hext,hterm,hiso⟩ := local_martingale_extension_of_integrable_variation_limit
    P F hF hle hnull (fun t ω => extendOpenPath (Y ω) t) B hY hB
    (fun n => realTimeClamp (c n)) hct.monotone hcut
    (fun t ht => by obtain ⟨n,hn⟩ := hcc t ht; exact ⟨n,hn.le⟩) CT hCT hBound hBlim
  have hall := terminal_l2_limit_all_times P F hF hle
    (fun t ω => extendOpenPath (Y ω) t) Ybar hYbar hext
  exact ⟨N,u,V,Z,Y,hu,hub,hVm,hZ,hY,hlim,Ybar,hYbar,⟨hext,hterm,hall,hiso⟩,B,hB,henergy,hprob⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_integral_constructed_with_terminal_isometry
