import Chapter8MobilityCoordinates

open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Matrix entries of an actual Euclidean linear operator reproduce its
action, including for a gradient represented in coordinate derivatives. -/
theorem euclidean_operator_matrix_action {d : ℕ}
    (M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    M x i=∑ j,M (EuclideanSpace.single j 1) i*x j := by
  have hx : x=∑ j,x j • EuclideanSpace.single j 1 := by
    ext k
    simp [Pi.single_apply]
  calc
    M x i=M (∑ j,x j • EuclideanSpace.single j 1) i := congrArg (fun y => M y i) hx
    _ = _ := by
      simp only [map_sum,map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem euclidean_operator_matrix_symmetric {d : ℕ}
    (M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hs : M.toLinearMap.IsSymmetric) (i j : Fin d) :
    M (EuclideanSpace.single j 1) i=M (EuclideanSpace.single i 1) j := by
  have hh := hs (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  change ⟪M (EuclideanSpace.single j 1),EuclideanSpace.single i 1⟫=
    ⟪EuclideanSpace.single j 1,M (EuclideanSpace.single i 1)⟫ at hh
  simpa only [EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_right,
    conj_trivial,one_mul,mul_one] using hh

end Asakura.Chapter8
