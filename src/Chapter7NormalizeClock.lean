import Chapter7ClockDensity
import Chapter7HalfLineEquality
import Chapter3ContinuousItoEnergy
import Chapter3InverseItoWeights
import Chapter3OpenProcessRegularity
import Chapter4BrownianSystem

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The last stochastic step of the time-change weak-solution proof.
From an actual local martingale whose bracket has derivative sigma²,
construct W = (1/sigma)·M, prove its Brownian covariance, and recover
M = sigma·W by the already constructed Ito associativity. -/
theorem normalize_clock_to_brownian
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (M A σ : HalfClosedTime → Ω → ℝ) (hM : LocalMProcessWitness P F M)
    (hA : LocalCovarianceWitness P F M M A)
    (hAm : ∀ w,MonotoneOn (fun t => A t w) (Iio ⊤))
    (hσa : ∀ t,t < ⊤ → Measurable[F t] (σ t))
    (hσc : ∀ w t,t < ⊤ → ContinuousAt (fun s => σ s w) t)
    (hσn : ∀ w t,t < ⊤ → σ t w ≠ 0)
    (hd : ∀ w r,0 < r → HasDerivAt (fun s => A (realTimeClamp s) w)
      ((σ (realTimeClamp r) w)^2) r) :
    ∃ B : BrownianSystem P 1, B.F = F ∧
      ItoCovarianceFormula P F M (fun z => 1/σ (realTimeClamp z.2) z.1) (B.W 0) ∧
      ∃ Z,LocalMProcessWitness P F Z ∧
        ItoCovarianceFormula P F (B.W 0) (fun z => σ (realTimeClamp z.2) z.1) Z ∧
        (∀ᵐ w ∂P,∀ t,t < ⊤ → Z t w = M t w) := by
  have hT : (0:EReal) < ⊤ := by simp
  have hAc := local_covariance_path_continuous P F M M A hM hM hA
  let H := fun t w => 1/σ t w
  have hHa t (ht : t < ⊤) : Measurable[F t] (H t) := measurable_const.div (hσa t ht)
  have hHc w t (ht : t < ⊤) : ContinuousAt (fun s => H s w) t :=
    continuousAt_const.div (hσc w t ht) (hσn w t ht)
  obtain ⟨hGa,hGc⟩ := open_process_real_regularity F H hHa hHc
  obtain ⟨hSa,hSc⟩ := open_process_real_regularity F σ hσa hσc
  obtain ⟨W,Z,hW,hZ,hWI,hZI,hZM⟩ := continuous_inverse_ito_weights_constructed P hT F hF hle hnull
    M hM (fun z => H (realTimeClamp z.2) z.1) (fun z => σ (realTimeClamp z.2) z.1)
    hGa hSa hGc hSc (by
      intro w r hr hrT
      dsimp only [H]
      field_simp [hσn w _ (changed_time_finite r hr)])
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨I,D,hIv,hIc,hI,hD,hDI⟩ := continuous_ito_energy_constructed P hT F hF hle hnull
    M A H W hM hA hAm hAc hHa hHc hW hWI c hc hcm hcT hct hcut hcc
  have hreg n := regular_covariance_on_real_intervals A hAm hAc (c n) (hc n).le (hcT n)
  have hIt (r : ℝ) (hr : 0 ≤ r) : I (realTimeClamp r) =ᵐ[P] fun _ => r := by
    obtain ⟨j,hj⟩ := hcc (realTimeClamp r) (changed_time_finite r hr)
    have hrj : r ≤ c j := by
      have hh := (changed_time_le_iff r hr _ (hcut j)).mp hj.le
      rwa [changed_time_real _ (hc j).le] at hh
    have hrreg := regular_covariance_on_real_intervals A hAm hAc r hr (EReal.coe_lt_top _)
    have he := positive_variation_integral_at_time P A I (fun z => H (realTimeClamp z.2) z.1^2)
      c (fun n => (hc n).le) hcT (fun n => (hreg n).1) (fun n => (hreg n).2) hI
      j r hr hrj hrreg.1 hrreg.2
    filter_upwards [he] with w hw
    rw [hw]
    simpa only [H,sub_zero] using inverse_coefficient_clock_energy 0 r hr
      (fun s => A (realTimeClamp s) w) (fun s => σ (realTimeClamp s) w)
      (hrreg.1 w) (hrreg.2 w) (hSc r hr (EReal.coe_lt_top _) w)
      (fun s hs => hσn w _ (changed_time_finite s hs.1)) (fun s hs => hd w s hs.1)
  let K := fun (t : HalfClosedTime) (_w : Ω) => (halfTimeReal t:ℝ)
  have hKc w t (ht : t < ⊤) : ContinuousAt (fun s => K s w) t := changed_time_coordinate_continuousAt t ht
  have hIK : ∀ᵐ w ∂P,∀ t,t < ⊤ → I t w = K t w :=
    half_line_common_equality P I K hIc hKc (by
      intro r hr
      simpa only [K,changed_time_real r hr] using hIt r hr)
  have hWK : LocalCovarianceWitness P F W W K := by
    refine ⟨Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hD.defect ?_ ?_ ?_,?_⟩
    · intro t ht
      exact ((hW.adapted P F t ht).mul (hW.adapted P F t ht)).sub measurable_const
    · intro w t ht
      exact ((hW.path P F w t ht).mul (hW.path P F w t ht)).sub (hKc w t ht)
    · filter_upwards [hDI,hIK] with w hdi hik
      intro t ht
      rw [hdi t ht,hik t ht]
    · exact (continuous_increasing_adapted_variation hT F hF K (fun _ _ => measurable_const)
        (fun w s hs t ht hst => half_time_real_mono hst ht) hKc).toPathwise
  let B : BrownianSystem P 1 := {
    F := F
    mono := hF
    le := hle
    null := hnull
    W := fun _ => W
    C := fun _ _ => K
    martingale := fun _ => hW
    cov := fun _ _ => hWK
    clock := by
      intro j k w r hr
      simp only [Subsingleton.elim j k,ite_true]
      exact changed_time_real r hr }
  exact ⟨B,rfl,hWI,Z,hZ,hZI,hZM⟩

end Asakura.Chapter7
