import Chapter8LipschitzTransition

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

/-- The variance estimate in the manuscript uses the uncentered second
moment m₂; the centered second moment from the copy argument is no larger. -/
theorem centered_second_moment_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure E) [IsProbabilityMeasure P]
    (hP : MemLp (fun x : E => x) 2 P) :
    (∫ x, ‖x-(∫ y,y ∂P)‖^2 ∂P) ≤ ∫ x, ‖x‖^2 ∂P := by
  let m := ∫ y,y ∂P
  have hi := hP.integrable (by norm_num)
  have hsq := (memLp_two_iff_integrable_sq_norm hP.aestronglyMeasurable).mp hP
  have hin : Integrable (fun x => ⟪m,x⟫) P := (innerSL ℝ m).integrable_comp hi
  have hmean : (∫ x, ⟪m,x⟫ ∂P) = ‖m‖^2 := by
    have hh := (innerSL ℝ m).integral_comp_comm hi
    change (∫ x, ⟪m,x⟫ ∂P) = ⟪m,m⟫ at hh
    rwa [real_inner_self_eq_norm_sq] at hh
  have he : (∫ x, ‖x-m‖^2 ∂P) = (∫ x, ‖x‖^2 ∂P)-‖m‖^2 := by
    simp_rw [norm_sub_sq_real,real_inner_comm m]
    have ht : Integrable (fun x => 2*⟪m,x⟫) P := hin.const_mul 2
    have hs : Integrable (fun x => ‖x‖^2-2*⟪m,x⟫) P := hsq.sub ht
    rw [integral_add hs (integrable_const _),
      integral_sub hsq ht,integral_const_mul,hmean,
      integral_const,probReal_univ,one_smul]
    ring
  change (∫ x, ‖x-m‖^2 ∂P) ≤ _
  rw [he]
  exact sub_le_self _ (sq_nonneg _)

end Asakura.Chapter8
