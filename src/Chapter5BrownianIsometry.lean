import Chapter5InfiniteBrownianIntegral
import Chapter5RepresentationExtension
import Chapter2ItoOperatorAssembly

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The isometry used in the representation theorem is the actual Brownian
integral on the complete progressive subspace. Its existence, linearity,
representative independence and norm identity are constructed. -/
theorem brownian_L2_isometry_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (hco : ∀ r,∃ n,r ≤ c n) :
    ∃ I : progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0))) →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∀ H : progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi 0))),
        ∃ M : ClosedTime T → Ω → ℝ,∃ hM : ContinuousM2Witness P F M,
          ItoCovarianceFormula P F W H.val M ∧
          I ⟨progressiveEnergyToLp F c _ H,LinearMap.mem_range_self _ H⟩ = (hM.moment ⊤).toLp (M ⊤) := by
  let ν := P.prod (volume.restrict (Ioi (0:ℝ)))
  have hex (H : progressiveEnergyIntegrands F c ν) :
      ∃ M : ClosedTime T → Ω → ℝ,∃ hM : ContinuousM2Witness P F M,
        ItoCovarianceFormula P F W H.val M ∧
        ‖(hM.moment ⊤).toLp (M ⊤)‖^2 = ‖progressiveEnergyToLp F c ν H‖^2 := by
    obtain ⟨M,hM,_,hMI,hiso,_⟩ := brownian_infinite_terminal_integral P hT F hF hle hnull W A hW hA
      c hc hcm hcT hct hcut hcc hclock H.val H.property.1 H.property.2.1 hco H.property.2.2
    have hsq := (memLp_two_iff_integrable_sq H.property.2.2.aestronglyMeasurable).mp H.property.2.2
    refine ⟨M,hM,hMI,?_⟩
    rw [hiso,← integral_prod _ hsq]
    exact (real_l2_norm_sq_integral ν H.val H.property.2.2).symm
  obtain ⟨L,hL⟩ := ito_operator_from_characterized_existence P hT F hF hle hnull W hW c ν hex
  let I : progressiveEnergyRange F c ν →ₗᵢ[ℝ] Lp ℝ 2 P :=
    { toLinearMap := (continuousM2Terminal P F).subtype.comp L.toLinearMap
      norm_map' := fun x => L.norm_map x }
  refine ⟨I,?_⟩
  intro H
  obtain ⟨M,hM,hMI,he⟩ := hL H
  refine ⟨M,hM,hMI,?_⟩
  exact congrArg Subtype.val he

end Asakura.Chapter5
