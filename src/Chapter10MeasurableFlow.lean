import Chapter10AdditivePathMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The additive solution family is jointly measurable in the starting
point and the random continuous forcing. Measurability of a stochastic
flow is derived here from measurable coordinates of the forcing. -/
theorem time_dependent_measurable_flow_exists {E Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω]
    (b : ℝ → E → E) (K : ℝ≥0) (hbc : Continuous (Function.uncurry b)) (hb : ∀ t,LipschitzWith K (b t))
    (W : ℝ → Ω → E) (hWm : ∀ t,Measurable (W t))
    (hWc : ∀ ω,Continuous (fun t => W t ω)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ X : E → ℝ → Ω → E,
      (∀ t,Measurable (fun p : E × Ω => X p.1 t p.2)) ∧
      (∀ x ω,Continuous (fun t => X x t ω)) ∧
      ∀ x ω t,t∈Icc 0 T → X x t ω=x+(∫ s in 0..t,b s (X x s ω))+W t ω := by
  obtain ⟨S,hSc,hS⟩ := time_dependent_additive_path_map_exists b K hbc hb T hT
  let V : Ω → C(Icc (0:ℝ) T,E) := fun ω =>
    ⟨fun t => W t.val ω,(hWc ω).comp continuous_subtype_val⟩
  have hVm : Measurable V := ContinuousMap.measurable_iff_eval.mpr (fun t => hWm t.val)
  let X := fun x t ω => S (x,V ω) (projIcc 0 T hT t)
  refine ⟨X,?_,?_,?_⟩
  · intro t
    exact (ContinuousMap.measurable_iff_eval.mp
      (hSc.measurable.comp (measurable_fst.prodMk (hVm.comp measurable_snd)))) _
  · intro x ω
    exact (S (x,V ω)).continuous.comp continuous_projIcc
  · intro x ω t ht
    have hp : projIcc 0 T hT t=⟨t,ht⟩ := by
      apply Subtype.ext
      simp [projIcc,ht.1,ht.2]
    change S (x,V ω) (projIcc 0 T hT t)=_
    rw [hp,hS]
    rfl

end Asakura.Chapter10
