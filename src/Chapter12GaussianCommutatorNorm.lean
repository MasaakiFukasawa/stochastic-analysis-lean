import Chapter12GaussianCommutatorCoordinates
import Chapter12FiniteArrayTriangle

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem gaussian_commutator_term_norm {n k : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (r : Fin (k+1)) (x : Fin (n+1) → ℝ) :
    Real.sqrt (∑ b : Fin (k+1) → Fin (n+1),
      ((u (b r)).iteratedPartial (List.ofFn (r.removeNth b))).f x^2)=
      gaussianDerivativeNorm u k x := by
  classical
  unfold gaussianDerivativeNorm gaussianArrayNorm
  congr 1
  rw [← Equiv.sum_comp (r.insertNthEquiv (fun _ : Fin (k+1) => Fin (n+1)))]
  conv_rhs => rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) => Fin (n+1)))]
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Fin.insertNthEquiv,Equiv.coe_fn_mk,Fin.insertNth_apply_same,Fin.removeNth_insertNth,
    gaussianDerivativeArray,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]

/-- The k corrections have norm at most k times the norm of D^(k-1)u;
there is no factor depending on the dimension of the Gaussian coordinates. -/
theorem gaussian_commutator_norm_bound {n k : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (x : Fin (n+1) → ℝ) :
    gaussianArrayNorm (fun b : Fin (k+1) → Fin (n+1) =>
      (GaussianJet.divergence u).iteratedPartial (List.ofFn b)) x ≤
      (k+1:ℕ)*gaussianDerivativeNorm u k x+
      gaussianArrayNorm (fun b : Fin (k+1) → Fin (n+1) =>
        GaussianJet.divergence (fun i => (u i).iteratedPartial (List.ofFn b))) x := by
  unfold gaussianArrayNorm
  simp only [gaussian_divergence_derivative_coordinates]
  have hh := finite_array_triangle
    (fun (r : Fin (k+1)) (b : Fin (k+1) → Fin (n+1)) =>
      ((u (b r)).iteratedPartial (List.ofFn (r.removeNth b))).f x)
    (fun b => (GaussianJet.divergence (fun i => (u i).iteratedPartial (List.ofFn b))).f x)
  simpa only [gaussian_commutator_term_norm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul] using hh

end Asakura.Chapter12
