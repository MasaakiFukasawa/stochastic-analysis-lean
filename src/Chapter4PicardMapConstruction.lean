import Chapter4ConstructedClockIto

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Construct the actual Picard map from a continuous adapted input.
The drift and Ito integrals are constructed by Chapter 2, and adaptation
and continuity of their sum are proved. This is the existence of the map;
the L2 difference bound and its fixed point are separate proof obligations. -/
theorem sde_picard_map_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (W C Y : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hC : LocalCovarianceWitness P F W W C)
    (hYm : ∀ t, t < ⊤ → Measurable[F t] (Y t))
    (hYc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => Y s ω) t)
    (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (ξ : Ω → ℝ) (hξ : Measurable[F ⊥] ξ)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcm : Monotone c)
    (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → C (realTimeClamp r) ω = r) :
    ∃ D Z : ClosedTime T → Ω → ℝ,
      AdaptedLocalVariationWitness F D ∧
      LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F W (fun z => σ (Y (realTimeClamp z.2) z.1)) Z ∧
      (∀ t, t < ⊤ → Measurable[F t] (fun ω => ξ ω+D t ω+Z t ω)) ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => ξ ω+D s ω+Z s ω) t) ∧
      ∀ᵐ ω ∂P, ∀ n d, d ∈ Icc 0 (c n) →
        ξ ω+D (realTimeClamp d) ω+Z (realTimeClamp d) ω =
          ξ ω+(∫ r in 0..d, μ (Y (realTimeClamp r) ω))+Z (realTimeClamp d) ω := by
  let H := fun t ω => μ (Y t ω)
  let K := fun t ω => σ (Y t ω)
  have hHm t ht : Measurable[F t] (H t) := hμ.measurable.comp (hYm t ht)
  have hHc ω t ht : ContinuousAt (fun s => H s ω) t := hμ.continuousAt.comp (hYc ω t ht)
  have hKm t ht : Measurable[F t] (K t) := hσ.measurable.comp (hYm t ht)
  have hKc ω t ht : ContinuousAt (fun s => K s ω) t := hσ.continuousAt.comp (hYc ω t ht)
  have hCv := covariance_adapted_variation P F hF hle hW hW hC
  have hCc ω t (ht : t < ⊤) : ContinuousAt (fun s => C s ω) t := by
    have hh := ((hW.path P F ω t ht).mul (hW.path P F ω t ht)).sub (hC.defect.path P F ω t ht)
    convert hh using 1
    funext s
    simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]
  obtain ⟨D,hD,hDc,hDI⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
    C hCv hCc (fun z => H (realTimeClamp z.2) z.1)
    (open_process_real_regularity F H hHm hHc).1 (open_process_real_regularity F H hHm hHc).2
  obtain ⟨Z,hZ,hZI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull W hW
    (fun z => K (realTimeClamp z.2) z.1)
    (open_process_real_regularity F K hKm hKc).1 (open_process_real_regularity F K hKm hKc).2
  refine ⟨D,Z,hD,hZ,hZI,?_,?_,?_⟩
  · intro t ht
    exact ((hξ.mono (hF bot_le) le_rfl).add (hD.adapted t ht)).add (hZ.adapted P F t ht)
  · intro ω t ht
    exact (continuousAt_const.add (hDc ω t ht)).add (hZ.path P F ω t ht)
  · filter_upwards [clock_variation_integral_all_times P C D _ c hc hcT hclock hDI] with ω hω
    intro n d hd
    rw [hω n d hd]

end Asakura.Chapter4
