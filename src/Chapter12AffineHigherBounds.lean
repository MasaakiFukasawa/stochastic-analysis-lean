import Chapter12InverseHigherDerivative

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1200000

theorem affine_all_higher_bounds {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (a : F) :
    ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀x,‖iteratedFDeriv ℝ k (fun z => a+L z) x‖≤C := by
  have hd : fderiv ℝ (fun z => a+L z)=fun _ : E => L := by
    funext x
    exact ((L.hasFDerivAt).const_add a).fderiv
  intro k hk
  by_cases hk1 : k=1
  · subst k
    refine ⟨‖L‖,norm_nonneg _,?_⟩
    intro x
    rw [norm_iteratedFDeriv_one,hd]
  · have hk2 : 2≤k := by omega
    obtain ⟨n,rfl⟩ : ∃n,k=n+2 := ⟨k-2,by omega⟩
    refine ⟨0,le_rfl,?_⟩
    intro x
    rw [←norm_iteratedFDeriv_fderiv,hd]
    simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,le_refl]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.affine_all_higher_bounds
