import Chapter12TensorCoordinateNorm

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem real_array_norm {I : Type*} [Fintype I] (f : I → ℝ) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℝ I)‖=Real.sqrt (∑ i,f i^2) := by
  simp only [EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs]

theorem finite_array_triangle {I J : Type*} [Fintype I] [Fintype J]
    (f : J → I → ℝ) (g : I → ℝ) :
    Real.sqrt (∑ i,((∑ j,f j i)+g i)^2) ≤
      (∑ j,Real.sqrt (∑ i,f j i^2))+Real.sqrt (∑ i,g i^2) := by
  classical
  let v : J → EuclideanSpace ℝ I := fun j => WithLp.toLp 2 (f j)
  let w : EuclideanSpace ℝ I := WithLp.toLp 2 g
  have he : WithLp.toLp 2 (fun i => (∑ j,f j i)+g i)=(∑ j,v j)+w := by
    apply PiLp.ext
    intro i
    simp [v,w]
  rw [← real_array_norm,he]
  apply (norm_add_le _ _).trans
  exact add_le_add (by simpa only [v,real_array_norm] using norm_sum_le Finset.univ v)
    (le_of_eq (real_array_norm g))

end Asakura.Chapter12
