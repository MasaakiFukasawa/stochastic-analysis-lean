import Chapter12GaussianTensorCoreNorm

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

/-- The recursive derivative coordinates agree with the explicit iterated
partial derivatives, including the order of all tensor indices. -/
theorem gaussianTensorJet_explicit {N : ℕ} (u : Fin N → GaussianJet N) (k : ℕ)
    (b : Fin (k+1) → Fin N) :
    gaussianTensorJet u k b=(u (b (Fin.last k))).iteratedPartial
      (List.ofFn (fun j : Fin k => b j.castSucc)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [gaussianTensorJet,ih,List.ofFn_succ]
    rfl

theorem gaussian_tensor_array_norm {n : ℕ} (u : Fin (n+1) → GaussianJet (n+1))
    (k : ℕ) (x : Fin (n+1) → ℝ) :
    gaussianArrayNorm (gaussianTensorJet u k) x=gaussianDerivativeNorm u k x := by
  classical
  unfold gaussianArrayNorm gaussianDerivativeNorm
  congr 1
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (k+1) => Fin (n+1)))]
  conv_rhs => rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) => Fin (n+1)))]
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  simp only [gaussianTensorJet_explicit,Fin.snocEquiv_apply,Fin.snoc_last,Fin.snoc_castSucc,
    gaussianDerivativeArray,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]

end Asakura.Chapter12
