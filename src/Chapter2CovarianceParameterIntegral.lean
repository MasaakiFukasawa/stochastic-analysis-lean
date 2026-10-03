import Chapter2SignedBochnerFubini
import Chapter2ItoCovarianceCharacterization

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The central displayed chain of the manuscript's Fubini proof, using
the actual covariance operator and the actual signed Stieltjes integrals.
No commutation theorem for the Ito operator is used. -/
theorem covariance_of_parameter_integral
    {E Ω : Type} [MeasurableSpace E] {m : MeasurableSpace Ω}
    (μ : Measure E) [SigmaFinite μ] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : ContinuousM2Witness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (α β : Ω → Measure ℝ) [∀ ω, IsFiniteMeasure (α ω)] [∀ ω, IsFiniteMeasure (β ω)]
    (ν : Ω → SignedMeasure ℝ) (hv : Measurable (fun ω => (ν ω).totalVariation))
    (hm : ∀ s t, Measurable (fun ω => ν ω (Ioc s t)))
    (hν0 : ∀ᵐ ω ∂P, (ν ω).totalVariation (Iic 0) = 0)
    (hν : ∀ ω a b, 0 ≤ a → a ≤ b → ν ω (Ioc a b) =
      C (min (realTimeClamp b) (realTimeClamp d)) ω-C (min (realTimeClamp a) (realTimeClamp d)) ω)
    (hc : ∀ᵐ ω ∂P, ∀ s t, s ≤ t → |ν ω (Ioc s t)| ≤
      Real.sqrt ((α ω).real (Ioc s t))*Real.sqrt ((β ω).real (Ioc s t)))
    (H : (E × Ω) × ℝ → ℝ) (hH : Measurable H)
    (hi : ∀ᵐ x ∂μ, ∀ᵐ ω ∂P, Integrable (fun r => H ((x,ω),r)^2) (α ω))
    (hAi : ∀ᵐ x ∂μ, Integrable (fun ω => ∫ r, H ((x,ω),r)^2 ∂α ω) P)
    (hBi : Integrable (fun ω => (β ω).real univ) P)
    (hN : Integrable (fun x => Real.sqrt (∫ ω, ∫ r, H ((x,ω),r)^2 ∂α ω ∂P)) μ)
    (Z : E → continuousM2Terminal P F) (hZ : Integrable Z μ)
    (hZI : ∀ᵐ x ∂μ, ItoCovarianceFormula P F X (fun z => H ((x,z.1),z.2))
      (m2ProcessOfTerminal P F (Z x))) :
    ∃ D, LocalCovarianceWitness P F (m2ProcessOfTerminal P F (∫ x, Z x ∂μ)) Y D ∧
      D (realTimeClamp d) =ᵐ[P]
        (fun ω => signedIntegralRaw (ν ω) (fun r => ∫ x, H ((x,ω),r) ∂μ)) := by
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  obtain ⟨u,hu,hut,huc⟩ := exists_strict_time_exhaustion hT
  have hYL := continuous_m2_is_local P F hF hle u hu.monotone hut huc Y hY
  obtain ⟨L,hL,hLI⟩ := actual_covariance_bochner_exchange P hT F hF hle hnull Y hY
    (realTimeClamp d) hdt
  obtain ⟨hLZ,D,hD,hDd⟩ := hLI E μ Z hZ
  have he : ∀ᵐ x ∂μ, ((L (Z x) : Lp ℝ 1 P) : Ω → ℝ) =ᵐ[P]
      (fun ω => signedIntegralRaw (ν ω) (fun r => H ((x,ω),r))) := by
    filter_upwards [hZI] with x hx
    obtain ⟨Cx,hCx,hLx⟩ := hL (Z x)
    obtain ⟨Dx,hDx,hform⟩ := hx Y C hYL hC
    obtain ⟨κ,hκ,hκ0,_,hκD⟩ := hform d hd hdT
    have heC := hCx.unique P F hF hle hDx
    filter_upwards [hLx,heC,hν0,hκ0,hκD] with ω hLω hCω hνω hκω hDω
    have heν : κ ω = ν ω := signed_measure_ext_positive_Ioc _ _ hκω hνω
      (fun a b ha hab => (hκ ω a b ha hab).trans (hν ω a b ha hab).symm)
    exact hLω.trans ((hCω _ hdt).trans (by simpa only [heν] using hDω))
  refine ⟨D,hD,hDd.trans ?_⟩
  exact signed_bochner_fubini_of_energy μ P α β ν hv hm hc H hH hi hAi hBi hN _ hLZ he

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.covariance_of_parameter_integral
