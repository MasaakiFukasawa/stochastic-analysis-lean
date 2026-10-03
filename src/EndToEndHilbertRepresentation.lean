import FullAuditOrthogonalDecomposition
import Mathlib.Analysis.Normed.Operator.Basic

open Set
open scoped RealInnerProductSpace
namespace Asakura.EndToEnd
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false

/-- The Appendix B proof: project one vector onto the kernel, then scale
its nonzero orthogonal component. Riesz representation is not an input. -/
theorem hilbert_representation_written {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (L : H →L[ℝ] ℝ) :
    ∃! z : H, (∀ f, L f = ⟪f,z⟫) ∧ ‖L‖ = ‖z‖ := by
  have exists_rep : ∃ z : H, ∀ f, L f = ⟪f,z⟫ := by
    by_cases hL : L = 0
    · exact ⟨0, by simp [hL]⟩
    obtain ⟨v,hv⟩ : ∃ v, L v ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hL (ContinuousLinearMap.ext hn)
    obtain ⟨⟨k,h⟩,⟨hk,hh,he⟩,_⟩ :=
      orthogonal_decomposition_written L.ker L.isClosed_ker v
    have hk0 : L k = 0 := hk
    have hlh : L h ≠ 0 := by
      have he' := congrArg L he
      simp only [map_add,hk0,zero_add] at he'
      rwa [← he']
    have hn : ‖h‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (by
      intro hz
      exact hlh (by simp [hz])))
    refine ⟨(L h / ‖h‖^2) • h,?_⟩
    intro f
    have hker : f - (L f / L h) • h ∈ L.ker := by
      change L (f - (L f / L h) • h) = 0
      simp [map_sub,map_smul,smul_eq_mul,hlh]
    have horth := hh _ hker
    have hi : ⟪f,h⟫ = (L f / L h) * ‖h‖^2 := by
      rw [real_inner_comm,inner_sub_left,inner_smul_left,real_inner_self_eq_norm_sq] at horth
      simpa using sub_eq_zero.mp horth
    rw [inner_smul_right,hi]
    have hn0 : ‖h‖ ≠ 0 := by intro hz; exact hn (by rw [hz]; norm_num)
    field_simp [hlh, hn0]
  obtain ⟨z,hz⟩ := exists_rep
  have hnorm : ‖L‖ = ‖z‖ := by
    apply le_antisymm
    · apply L.opNorm_le_bound (norm_nonneg z)
      intro f
      rw [hz f,Real.norm_eq_abs,mul_comm]
      exact abs_real_inner_le_norm f z
    · have he := L.le_opNorm z
      rw [hz z,real_inner_self_eq_norm_sq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at he
      by_cases hzero : z = 0
      · simp [hzero]
      · have hp : 0 < ‖z‖ := norm_pos_iff.mpr hzero
        nlinarith
  refine ⟨z,⟨hz,hnorm⟩,?_⟩
  intro w hw
  exact ext_inner_left ℝ (fun f => (hw.1 f).symm.trans (hz f))

#print axioms hilbert_representation_written
end Asakura.EndToEnd
