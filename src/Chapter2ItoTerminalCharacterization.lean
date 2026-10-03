import Chapter2ItoConstructionIsometry
import Chapter2ItoApproximationCharacterization
import Chapter2LocalCovarianceAE
import Chapter2LevelLocalization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- One and the same concrete continuous M2 martingale satisfies both the
covariance characterization and the terminal isometry. Its terminal value
is constructed as a limit and never assumed in the input. -/
theorem ito_terminal_isometry_and_covariance_constructed
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
    ∃ Ybar : ClosedTime T → Ω → ℝ, ∃ hYbar : ContinuousM2Witness P F Ybar,
      LocalMProcessWitness P F Ybar ∧ ItoCovarianceFormula P F X H Ybar ∧
      ‖(hYbar.moment ⊤).toLp (Ybar ⊤)‖^2 = ∫ ω, CT ω ∂P ∧
      ∃ Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ),
        (∀ t, t < ⊤ → Ybar t =ᵐ[P] (fun ω => extendOpenPath (Y ω) t)) ∧
        Tendsto (fun t => eLpNorm ((fun ω => extendOpenPath (Y ω) t)-Ybar ⊤) 2 P)
          (𝓝[<] (⊤ : ClosedTime T)) (𝓝 0) := by
  classical
  obtain ⟨N,u,V,Z,Y,hu,hub,hVm,hZ,hY,hlim,Ybar,hYbar,hext,B,hB,henergy,hprob⟩ :=
    ito_integral_constructed_with_terminal_isometry P hT F hF hle hnull X A hX hA
      c hc hcm hcT hct hcut hcc hAm hAc H hH hi CT hCT hCTlim
  have hchar := ito_approximation_covariance_characterization P hT F hF hle hnull X A hX hA
    c hc hcm hcT hct hcut hcc hAm hAc H hH hi N u V Z Y hu hub hVm hZ hY hlim hprob
  have hbarlocal := continuous_m2_is_local P F hF hle (fun n => realTimeClamp (c n))
    hct.monotone hcut hcc Ybar hYbar
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  have he : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → extendOpenPath (Y ω) t = Ybar t ω := by
    have h := continuous_process_common_time_equality P
      (fun t : Iio (⊤ : ClosedTime T) => fun ω => Y ω t)
      (fun t : Iio (⊤ : ClosedTime T) => Ybar t.val)
      (fun ω => (Y ω).continuous) (fun ω => (hYbar.path ω).comp continuous_subtype_val) ?_
    · exact h.mono (fun ω hω t ht => by
        simpa only [extendOpenPath,dif_pos ht] using hω ⟨t,ht⟩)
    · intro t
      filter_upwards [(hext.1 t.val t.property).symm] with ω hω
      change (if ht : t.val ∈ Iio (⊤ : ClosedTime T) then Y ω ⟨t.val,ht⟩ else 0) = Ybar t.val ω at hω
      rw [dif_pos t.property] at hω
      exact hω
  refine ⟨Ybar,hYbar,hbarlocal,?_,hext.2.2.2,Y,hext.1,hext.2.2.1⟩
  intro Y0 C0 hY0 hC0
  obtain ⟨D,hD,hformula⟩ := hchar Y0 C0 hY0 hC0
  exact ⟨D,hD.congr_ae_processes P F hF hle hY hY0 hbarlocal hY0 he
    (ae_of_all _ (fun _ _ _ => rfl)),hformula⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_terminal_isometry_and_covariance_constructed
