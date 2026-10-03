import Chapter2VariationStoppedRemainder
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The finite-horizon C1 example includes adaptedness of the increasing
parts, which does not follow just by writing a pathwise Jordan decomposition. -/
theorem differentiable_adapted_process_in_variation_space
    {Ω : Type*} (b : ℝ) [Fact (0 ≤ b)]
    (F : Icc (0:ℝ) b → MeasurableSpace Ω) (hF : Monotone F)
    (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, ContDiffOn ℝ 1 (A ω) (Icc 0 b))
    (had : ∀ t : Icc (0:ℝ) b, Measurable[F t] (fun ω => A ω t.val)) :
    ∃ U V : Icc (0:ℝ) b → Ω → ℝ,
      (∀ t, Measurable[F t] (U t)) ∧ (∀ t, Measurable[F t] (V t)) ∧
      (∀ ω, Continuous (fun t => U t ω)) ∧ (∀ ω, Continuous (fun t => V t ω)) ∧
      (∀ ω, Monotone (fun t => U t ω)) ∧ (∀ ω, Monotone (fun t => V t ω)) ∧
      ∀ t ω, A ω t.val = U t ω-V t ω := by
  let X := fun t : Icc (0:ℝ) b => fun ω => A ω t.val
  have hc ω : Continuous (fun t => X t ω) := (hA ω).continuousOn.restrict
  have hb ω : BoundedVariationOn (fun t => X t ω) univ := by
    obtain ⟨K,hK⟩ := (hA ω).exists_lipschitzOnWith (by norm_num) (convex_Icc 0 b) isCompact_Icc
    have hB : BoundedVariationOn (A ω) (Icc 0 b) :=
      hK.comp_boundedVariationOn (mapsTo_id _) (BoundedVariationOn.id_Icc 0 b)
    have he := eVariationOn.comp_eq_of_monotoneOn (t := univ) (A ω)
      (Subtype.val : Icc (0:ℝ) b → ℝ) (fun _ _ _ _ h => h)
    change eVariationOn (fun t => X t ω) univ ≠ ∞
    simp only [Function.comp_def,image_univ,Subtype.range_coe_subtype,setOf_mem_eq] at he
    exact he.trans_ne hB
  let W := fun t ω => pathVariation (fun s => X s ω) t
  have hWm t : Measurable[F t] (W t) := variation_process_adapted F hF X had hc t
  have hWc ω : Continuous (fun t => W t ω) := variation_process_continuous _ (hb ω) (hc ω)
  refine ⟨fun t ω => (W t ω+X t ω)/2,fun t ω => (W t ω-X t ω)/2,
    fun t => ((hWm t).add (had t)).div_const 2,
    fun t => ((hWm t).sub (had t)).div_const 2,
    fun ω => ((hWc ω).add (hc ω)).div_const 2,
    fun ω => ((hWc ω).sub (hc ω)).div_const 2,?_,?_,?_⟩
  · intro ω s t hst
    exact div_le_div_of_nonneg_right ((path_variation_add_sub_monotone _ (hb ω)).1 hst) (by norm_num)
  · intro ω s t hst
    exact div_le_div_of_nonneg_right ((path_variation_add_sub_monotone _ (hb ω)).2 hst) (by norm_num)
  · intro t ω
    change X t ω = _
    ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.differentiable_adapted_process_in_variation_space
