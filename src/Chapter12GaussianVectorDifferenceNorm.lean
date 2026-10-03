import Chapter12GaussianVectorFunction

namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_vector_derivative_difference_norm {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} (u v : Fin N → GaussianJet N) (e : Fin N → H) (he : Orthonormal ℝ e)
    (k : ℕ) (x : Fin N → ℝ) :
    Real.sqrt (∑a:Fin k → Fin N,
      ‖iteratedFDeriv ℝ k (gaussianVectorFunction u e) x (fun j => Pi.single (a j) 1)-
        iteratedFDeriv ℝ k (gaussianVectorFunction v e) x (fun j => Pi.single (a j) 1)‖^2)=
      Real.sqrt (∑a:Fin (k+1) → Fin N,((gaussianTensorJet u k a).f x-(gaussianTensorJet v k a).f x)^2) := by
  classical
  simp_rw [gaussianVectorFunction_derivative,←Finset.sum_sub_distrib,←sub_smul,
    orthonormal_sum_norm e he,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  congr 1
  rw [←Equiv.sum_comp (Fin.snocEquiv (fun _:Fin (k+1) => Fin N)),Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  simp only [gaussianTensorJet_explicit,Fin.snocEquiv_apply,Fin.snoc_last,Fin.snoc_castSucc]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.gaussian_vector_derivative_difference_norm
