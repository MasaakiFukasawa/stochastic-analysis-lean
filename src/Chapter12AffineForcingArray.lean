import Chapter12AffineHigherBounds
import Chapter12ContinuousMapOperator

open scoped Topology ContDiff BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem affine_higher_derivative_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (a : F) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ (n+2) (fun z => a+L z) x=0 := by
  apply norm_eq_zero.mp
  rw [←norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ (fun z => a+L z)=fun _ : E => L := by
    funext y
    exact (L.hasFDerivAt.const_add a).fderiv
  rw [he]
  simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]

theorem affine_forcing_array_bounds {n : ℕ} {K E : Type*}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (Fin n → ℝ) →L[ℝ] C(K,E)) (a : C(K,E)) (B : ℝ) (hB : 0≤B)
    (hb : ∀t,Real.sqrt (∑i,‖L (Pi.single i 1) t‖^2)≤B)
    (k : ℕ) (hk : 1≤k) (z : Fin n → ℝ) (t : K) :
    Real.sqrt (∑i : Fin k → Fin n,
      ‖(iteratedFDeriv ℝ k (fun y => a+L y) z (fun j => Pi.single (i j) 1)) t‖^2)≤
      (if k=1 then B else 0) := by
  classical
  by_cases hk1 : k=1
  · subst k
    rw [if_pos rfl]
    simp only [iteratedFDeriv_one_apply,(L.hasFDerivAt.const_add a).fderiv]
    have he := (Equiv.funUnique (Fin 1) (Fin n)).sum_comp (fun i => ‖L (Pi.single i 1) t‖^2)
    change (∑i : Fin 1 → Fin n,‖L (Pi.single (i 0) 1) t‖^2)=(∑i : Fin n,‖L (Pi.single i 1) t‖^2) at he
    rw [he]
    exact hb t
  · obtain ⟨m,rfl⟩ : ∃m,k=m+2 := ⟨k-2,by omega⟩
    rw [affine_higher_derivative_zero,if_neg (by omega)]
    simp
end Asakura.Chapter12
#print axioms Asakura.Chapter12.affine_forcing_array_bounds
