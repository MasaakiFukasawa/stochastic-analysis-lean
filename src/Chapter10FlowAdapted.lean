import Chapter10LinearCausality
import Chapter10AdditivePathMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter10
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Adaptation follows from the continuous solution map on each past interval
and pathwise uniqueness; it is not assumed as part of the constructed flow. -/
theorem time_dependent_flow_adapted {Ω E : Type*} {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (F : ℝ → MeasurableSpace Ω) (hF : Monotone F)
    (b : ℝ → E → E) (K : ℝ≥0) (hbc : Continuous (Function.uncurry b))
    (hb : ∀ s,LipschitzWith K (b s))
    (ξ : Ω → E) (hξ : Measurable[F 0] ξ)
    (X W : ℝ → Ω → E) (hcX : ∀ w,Continuous (fun s => X s w))
    (hcW : ∀ w,Continuous (fun s => W s w))
    (T : ℝ) (hW : ∀ s∈Icc 0 T,Measurable[F s] (W s))
    (he : ∀ w s,s∈Icc 0 T → X s w=ξ w+(∫ u in 0..s,b u (X u w))+W s w) :
    ∀ t∈Icc 0 T,Measurable[F t] (X t) := by
  intro t ht
  letI : MeasurableSpace Ω := F t
  let Z : Ω → C(Icc (0:ℝ) t,E) := fun w =>
    ⟨fun s => W s.val w,(hcW w).comp continuous_subtype_val⟩
  have hZm : Measurable[F t] Z := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro s
    exact (hW s.val ⟨s.property.1,s.property.2.trans ht.2⟩).mono (hF s.property.2) le_rfl
  obtain ⟨S,hSc,hS⟩ := time_dependent_additive_path_map_exists b K hbc hb t ht.1
  let R := fun w s => S (ξ w,Z w) (projIcc 0 t ht.1 s)
  have hRm : Measurable[F t] (fun w => R w t) :=
    (continuous_eval_const (projIcc 0 t ht.1 t)).measurable.comp
      (hSc.measurable.comp ((hξ.mono (hF ht.1) le_rfl).prodMk hZm))
  have hEq (w : Ω) : X t w=R w t := by
    apply time_dependent_solution_causal b K hbc hb (fun s => X s w) (R w)
      (fun s => W s w) (fun s => W s w) (hcX w)
      ((S (ξ w,Z w)).continuous.comp continuous_projIcc) (ξ w) t ht.1
      (fun _ _ => rfl) (fun s hs => he w s ⟨hs.1,hs.2.trans ht.2⟩) ?_ t ⟨ht.1,le_rfl⟩
    intro s hs
    have hp : projIcc 0 t ht.1 s=⟨s,hs⟩ := Subtype.ext (by simp [projIcc,hs.1,hs.2])
    change S (ξ w,Z w) (projIcc 0 t ht.1 s)=_
    rw [hp,hS]
    rfl
  have hfun : X t=(fun w => R w t) := funext hEq
  rw [hfun]
  exact hRm

end Asakura.Chapter10
