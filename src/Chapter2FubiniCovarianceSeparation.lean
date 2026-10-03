import Chapter2CovarianceParameterIntegral
import Chapter2CanonicalFubiniData
import Chapter2GlobalEnergyHorizon

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Once the two M2 integrals have been constructed, the manuscript's
covariance proof identifies them. Every finite-horizon Fubini hypothesis
is derived from the original global mixed energy condition. -/
theorem stochastic_fubini_by_covariance_separation
    {E Ω : Type} [MeasurableSpace E] {m : MeasurableSpace Ω}
    (μ : Measure E) [SigmaFinite μ] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hAr : ∀ r, Measurable (fun ω => A (realTimeClamp r) ω))
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (ν : Measure (Ω × ℝ)) [SigmaFinite ν]
    (henergy : ∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ∂ν) = ∫⁻ ω, ⨆ n, ∫⁻ r, f (ω,r)
        ∂(intervalStieltjes 0 (c n) (hc n) (fun r => A (realTimeClamp r) ω)
          ((regular_covariance_on_real_intervals A hAm hAc (c n) (hc n) (hcT n)).1 ω)
          (fun r hr => ((regular_covariance_on_real_intervals A hAm hAc (c n) (hc n) (hcT n)).2 ω r hr).mono inter_subset_left)).measure ∂P)
    (H : E × (Ω × ℝ) → ℝ) (hH : Measurable H)
    (hN : (∫⁻ x, eLpNorm (fun z => H (x,z)) 2 ν ∂μ) < ∞)
    (Z : E → continuousM2Terminal P F) (hZ : Integrable Z μ)
    (hZI : ∀ᵐ x ∂μ, ItoCovarianceFormula P F X (fun z => H (x,z))
      (m2ProcessOfTerminal P F (Z x)))
    (W : ClosedTime T → Ω → ℝ) (hW : ContinuousM2Witness P F W)
    (hWI : ItoCovarianceFormula P F X (fun z => ∫ x, H (x,z) ∂μ) W) :
    ∀ᵐ ω ∂P, ∀ t, m2ProcessOfTerminal P F (∫ x, Z x ∂μ) t ω = W t ω := by
  let N := m2ProcessOfTerminal P F (∫ x, Z x ∂μ)
  have hN2 : ContinuousM2Witness P F N := (m2_process_of_terminal_spec P F _).1
  obtain ⟨u,hu,hum,huT⟩ := exists_seq_strictMono_tendsto' (show (⊥ : ClosedTime T) < ⊤ from hT)
  have huc : ∀ t, t < ⊤ → ∃ n, t < u n := fun t ht => (huT.eventually (lt_mem_nhds ht)).exists
  have hNL := continuous_m2_is_local P F hF hle u hu.monotone (fun n => (hum n).2) huc N hN2
  have hWL := continuous_m2_is_local P F hF hle u hu.monotone (fun n => (hum n).2) huc W hW
  have he : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → N t ω = W t ω := by
    apply local_covariance_separates_m2_tests P F hF hle hnull N W hNL hWL
    intro Y hY2
    have hYL := continuous_m2_is_local P F hF hle u hu.monotone (fun n => (hum n).2) huc Y hY2
    obtain ⟨B,hB,hBm,hBc,hB0,_⟩ := quadratic_variation_measurable_encoding P hT F hF hle hnull Y hYL
    obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull X Y hX hYL
    obtain ⟨D,hD⟩ := local_covariance_witness_exists P F hF hle hnull N Y hNL hYL
    obtain ⟨R,hR,hRf⟩ := hWI Y C hYL hC
    refine ⟨D,R,hD,hR,?_⟩
    apply local_covariance_common_time_equality P hT F N Y D R hNL hYL hD
      (hR.continuous_open_paths P F W Y R hWL hYL)
    intro t ht
    obtain ⟨d,hd,hdT,rfl⟩ := finite_closed_time_real t ht
    have hdt : realTimeClamp (T := T) d < ⊤ := by
      change (realTimeClamp d : EReal) < T
      rw [real_time_clamp_eq d hd hdT.le]
      exact hdT
    obtain ⟨n,hn⟩ := hcc _ hdt
    have hdn : d ≤ c n := by
      have hh : (realTimeClamp (T := T) d : EReal) < (realTimeClamp (T := T) (c n) : EReal) := hn
      rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c n) (hc n) (hcT n).le] at hh
      exact (EReal.coe_lt_coe_iff.mp hh).le
    let hmA := (regular_covariance_on_real_intervals A hAm hAc d hd hdT).1
    let hcA := (regular_covariance_on_real_intervals A hAm hAc d hd hdT).2
    let hmB := (regular_covariance_on_real_intervals B hBm hBc d hd hdT).1
    let hcB := (regular_covariance_on_real_intervals B hBm hBc d hd hdT).2
    let α := fun ω => (intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hmA ω)
      (fun r hr => (hcA ω r hr).mono inter_subset_left)).measure
    let β := fun ω => (intervalStieltjes 0 d hd (fun r => B (realTimeClamp r) ω) (hmB ω)
      (fun r hr => (hcB ω r hr).mono inter_subset_left)).measure
    letI : ∀ ω, IsFiniteMeasure (α ω) := fun ω => intervalStieltjes_finite _ _ _ _ _ _
    letI : ∀ ω, IsFiniteMeasure (β ω) := fun ω => intervalStieltjes_finite _ _ _ _ _ _
    let κ := randomStieltjesKernel 0 d hd (fun ω r => A (realTimeClamp r) ω) hmA
      (fun ω r hr => (hcA ω r hr).mono inter_subset_left) hAr
    have hκ ω : IsFiniteMeasure (κ ω) := show IsFiniteMeasure (α ω) from inferInstance
    have hdom := global_stieltjes_finite_horizon_domination P ν c hc
      (fun ω r => A (realTimeClamp r) ω)
      (fun n => (regular_covariance_on_real_intervals A hAm hAc (c n) (hc n) (hcT n)).1)
      (fun n => (regular_covariance_on_real_intervals A hAm hAc (c n) (hc n) (hcT n)).2)
      henergy d hd n hdn hmA hcA
    obtain ⟨hi,hAi,hNi⟩ := finite_kernel_parameter_energy μ P ν κ hκ hdom H hH hN
    have hBi := m2_quadratic_stieltjes_mass_integrable P F hF hle hnull Y B hYL hY2 hB d hd hdT hmB hcB
    obtain ⟨ξ,hcs,hξ,hβm,hξv,hξm,hξ0⟩ := canonical_covariance_measure_fubini_data P F hF hle hnull
      X Y A B C hX hYL hA hB hC d hd hdT hmA hmB hcA hcB
    have hH' : Measurable (fun z : (E × Ω) × ℝ => H (z.1.1,(z.1.2,z.2))) :=
      hH.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    obtain ⟨D',hD',heD'⟩ := covariance_of_parameter_integral μ P hT F hF hle hnull X Y C hX hY2 hC
      d hd hdT α β ξ hξv hξm hξ0 hξ hcs _ hH' hi hAi hBi hNi Z hZ hZI
    obtain ⟨η,hη,hη0,_,heR⟩ := hRf d hd hdT
    have heD := hD.unique P F hF hle hD'
    filter_upwards [heD,heD',heR,hξ0,hη0] with ω heDω hDω hRω hξω hηω
    have heξ : ξ ω = η ω := signed_measure_ext_positive_Ioc _ _ hξω hηω
      (fun a b ha hab => (hξ ω a b ha hab).trans (hη ω a b ha hab).symm)
    exact (heDω _ hdt).trans (hDω.trans (by simpa only [heξ] using hRω.symm))
  filter_upwards [he] with ω hω
  intro t
  by_cases ht : t < ⊤
  · exact hω t ht
  · have htop : t = ⊤ := eq_top_iff.mpr (le_of_not_gt ht)
    rw [htop]
    have hnT := ((hN2.path ω).continuousAt.tendsto (x := ⊤)).comp huT
    have hwT := ((hW.path ω).continuousAt.tendsto (x := ⊤)).comp huT
    exact tendsto_nhds_unique (hnT.congr (fun n => hω (u n) (hum n).2)) hwT

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stochastic_fubini_by_covariance_separation
