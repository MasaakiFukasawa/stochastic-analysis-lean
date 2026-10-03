import Chapter12ScalarPathArrayDifference

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem scalar_path_derivative {K E G : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (X : G → C(K,E)) (hX : ContDiff ℝ ∞ X) (ell : E →L[ℝ] ℝ)
    (k : ℕ) (z : G) (v : Fin k → G) (t : K) :
    (iteratedFDeriv ℝ k (fun y => ell.compLeftContinuous ℝ K (X y)) z v) t=
      ell ((iteratedFDeriv ℝ k X z v) t) := by
  exact congrArg (fun D => D v t)
    ((ell.compLeftContinuous ℝ K).iteratedFDeriv_comp_left hX.contDiffAt (by simp))

theorem scalar_path_derivative_array_bound {K E G I : Type*}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype I]
    (X : G → C(K,E)) (hX : ContDiff ℝ ∞ X) (ell : E →L[ℝ] ℝ)
    (k : ℕ) (z : G) (v : I → Fin k → G) (t : K) :
    Real.sqrt (∑i,‖(iteratedFDeriv ℝ k (fun y => ell.compLeftContinuous ℝ K (X y)) z (v i)) t‖^2)≤
      ‖ell‖*Real.sqrt (∑i,‖(iteratedFDeriv ℝ k X z (v i)) t‖^2) := by
  simp_rw [scalar_path_derivative X hX ell]
  exact linear_array_bound ell _
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_path_derivative_array_bound
