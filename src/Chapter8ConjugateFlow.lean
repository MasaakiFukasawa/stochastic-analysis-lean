import FullAuditTransportFlow

open MeasureTheory
namespace Asakura.Chapter8
open Asakura.FullAudit

/-- Change of coordinates commutes with applying a random flow. -/
theorem conjugate_flow_law {E G Ω : Type*} [MeasurableSpace E]
    [MeasurableSpace G] [MeasurableSpace Ω]
    (A : E ≃ᵐ G) (μ : Measure E) (P : Measure Ω) [SFinite μ] [SFinite P]
    (F : E → Ω → E) (hF : Measurable (Function.uncurry F)) :
    (flowLaw μ P F).map A =
      flowLaw (μ.map A) P (fun x ω => A (F (A.symm x) ω)) := by
  have hG : Measurable (fun z : G × Ω => A (F (A.symm z.1) z.2)) :=
    A.measurable.comp (hF.comp ((A.symm.measurable.comp measurable_fst).prodMk measurable_snd))
  unfold flowLaw
  rw [Measure.map_map A.measurable hF]
  have he : (μ.map A).prod P = (μ.prod P).map (Prod.map A id) := by
    simpa using Measure.map_prod_map μ P A.measurable measurable_id
  rw [he]
  change Measurable (Function.uncurry (fun x ω => A (F (A.symm x) ω))) at hG
  rw [Measure.map_map hG (A.measurable.prodMap measurable_id)]
  congr 1
  funext z
  simp [Function.uncurry,Prod.map]

/-- A shared-noise contraction in transformed coordinates gives the
Wasserstein contraction for the corresponding quadratic distance. -/
theorem conjugate_shared_noise_contraction {E G Ω : Type*}
    [MeasurableSpace E] [NormedAddCommGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] [MeasurableSpace Ω]
    (A : E ≃ᵐ G) (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : E → Ω → E) (hF : Measurable (Function.uncurry F))
    (hμ : MemLp (fun x : G => x) 2 (μ.map A))
    (hν : MemLp (fun x : G => x) 2 (ν.map A))
    (a : ℝ) (ha : 0 < a)
    (hLip : ∀ x y, ∀ᵐ ω ∂P, ‖A (F x ω)-A (F y ω)‖ ≤ a*‖A x-A y‖) :
    transportDistance ((flowLaw μ P F).map A) ((flowLaw ν P F).map A) ≤
      a*transportDistance (μ.map A) (ν.map A) := by
  let H : G → Ω → G := fun x ω => A (F (A.symm x) ω)
  have hH : Measurable (Function.uncurry H) :=
    A.measurable.comp (hF.comp ((A.symm.measurable.comp measurable_fst).prodMk measurable_snd))
  have hHL : ∀ x y, ∀ᵐ ω ∂P, ‖H x ω-H y ω‖ ≤ a*‖x-y‖ := by
    intro x y
    simpa only [H,A.apply_symm_apply] using hLip (A.symm x) (A.symm y)
  haveI := quadratic_coupling_nonempty (μ.map A) (ν.map A) hμ hν
  rw [conjugate_flow_law A μ P F hF,conjugate_flow_law A ν P F hF]
  exact shared_noise_transport_contraction (μ.map A) (ν.map A) P H hH a ha hHL

end Asakura.Chapter8
