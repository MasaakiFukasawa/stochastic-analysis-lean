import Chapter4NormalCDF

namespace Asakura.Chapter5

noncomputable def coleHopf (a : ℝ) (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.log (q x)/a

/-- Differentiate the actual logarithmic transform, not an assigned derivative. -/
theorem coleHopf_derivative (a x qx : ℝ) (q : ℝ → ℝ)
    (hq : HasDerivAt q qx x) (hp : q x ≠ 0) :
    HasDerivAt (coleHopf a q) (qx/(a*q x)) x := by
  convert (hq.log hp).div_const a using 1 <;> first | rfl | ring

/-- The PDE transformation after the heat equation, at a point where q>0. -/
theorem coleHopf_heat_equation (a q qt qx qxx : ℝ)
    (ha : a ≠ 0) (hq : q ≠ 0) (hheat : qt = qxx/2) :
    qt/(a*q) = (qxx/(a*q)-qx^2/(a*q^2))/2 +
      a/2*(qx/(a*q))^2 := by
  rw [hheat]
  field_simp
  <;> ring

/-- Differentiating the heat equation and the quotient gives the Burgers
nonlinearity with coefficient a, including its sign. -/
theorem coleHopf_burgers_equation (a q qx qxx qxxx qt qxt : ℝ)
    (ha : a ≠ 0) (hq : q ≠ 0)
    (hheat : qt = qxx/2) (hheatx : qxt = qxxx/2) :
    (qxt*q-qx*qt)/(a*q^2) =
      (qxxx/q-3*qx*qxx/q^2+2*qx^3/q^3)/(2*a) +
      a*(qx/(a*q))*((qxx*q-qx^2)/(a*q^2)) := by
  rw [hheat,hheatx]
  field_simp
  <;> ring

/-- The log transform recovers the terminal payoff exactly. -/
theorem coleHopf_terminal (a f : ℝ) (ha : a ≠ 0) :
    Real.log (Real.exp (a*f))/a = f := by
  rw [Real.log_exp]
  field_simp

/-- The logarithmic Ito correction for the actual integrand a X Z. -/
theorem coleHopf_ito_coefficients (a x z : ℝ) (ha : a ≠ 0) (hx : x ≠ 0) :
    (1/(a*x))*(a*x*z) = z ∧
    (-1/(a*x^2))/2*(a*x*z)^2 = -(a/2)*z^2 := by
  constructor <;> field_simp <;> ring

end Asakura.Chapter5
