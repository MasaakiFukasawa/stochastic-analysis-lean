import Mathlib.Analysis.Calculus.Deriv.Inv

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- The diagonal gamma correction comes from differentiating 1/x_i.
For i different from j the denominator is constant. -/
theorem gamma_denominator_derivative {ι : Type*} [DecidableEq ι]
    (i j : ι) (x : ι → ℝ) (hi : x i≠0) (hj : x j≠0)
    (F : ℝ → ℝ) (J : ℝ) (hF : HasDerivAt F (J/x j) (x j)) :
    HasDerivAt (fun u => F u/(if i=j then u else x i))
      ((J-(if i=j then F (x j) else 0))/(x i*x j)) (x j) := by
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    have hh := hF.div (hasDerivAt_id (x i)) hi
    convert hh using 1
    · rfl
    · simp only [id_eq,mul_one]
      field_simp [hi]
      <;> ring
  · simp only [hij,ite_false,sub_zero]
    convert hF.div_const (x i) using 1
    field_simp
    <;> ring

end Asakura.Chapter12
