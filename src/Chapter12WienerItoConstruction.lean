import Chapter12DeterministicEnergy
import Chapter5BrownianIsometry
import Chapter4BrownianSystem

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Construct the deterministic Wiener isometry by restricting the already
constructed Ito integral to deterministic L2 time functions. -/
theorem wiener_isometry_from_actual_ito {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcut : ∀ n, realTimeClamp (T := ⊤) (c n) < ⊤)
    (hcc : ∀ t : HalfClosedTime, t < ⊤ → ∃ n, t < realTimeClamp (c n))
    (hco : ∀ r : ℝ, ∃ n, r ≤ c n) :
    ∃ W : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∀ f : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))),
      ∃ M : HalfClosedTime → Ω → ℝ, ∃ hM : ContinuousM2Witness P B.F M,
        ItoCovarianceFormula P B.F (B.W 0) (fun z => f z.2) M ∧
        W f = (hM.moment ⊤).toLp (M ⊤) := by
  obtain ⟨I,hI⟩ := brownian_L2_isometry_constructed P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    c hc hcm (fun n => EReal.coe_lt_top _) hct hcut hcc
    (fun n w r hr => B.diagonal_clock 0 w r hr.1) hco
  let W := I.comp (deterministicEnergyEmbedding P B.F c)
  refine ⟨W,fun f => ?_⟩
  obtain ⟨M,hM,hMI,he⟩ := hI (deterministicEnergyIntegrand P B.F c f)
  refine ⟨M,hM,hMI,?_⟩
  change I (deterministicEnergyEmbedding P B.F c f) = _
  rw [deterministic_energy_realization]
  exact he

end Asakura.Chapter12
