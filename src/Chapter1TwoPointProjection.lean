import FullAuditDiceExercise
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter1Complete

noncomputable def twoPointLaw (p : ℝ) : Measure (Fin 2) :=
  ENNReal.ofReal p • Measure.dirac 0+ENNReal.ofReal (1-p) • Measure.dirac 1

theorem two_point_integral (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (X : Fin 2 → ℝ) :
    (∫ w,X w ∂twoPointLaw p)=p*X 0+(1-p)*X 1 := by
  unfold twoPointLaw
  rw [integral_add_measure ((Integrable.of_finite (μ := Measure.dirac (0:Fin 2))).smul_measure ENNReal.ofReal_ne_top) ((Integrable.of_finite (μ := Measure.dirac (1:Fin 2))).smul_measure ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure,ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal (sub_nonneg.mpr hp1),smul_eq_mul]

theorem two_point_inner_product (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (X Y : Fin 2 → ℝ) :
    (X 0*Real.sqrt p)*(Y 0*Real.sqrt p)+
      (X 1*Real.sqrt (1-p))*(Y 1*Real.sqrt (1-p))=
      ∫ w,X w*Y w ∂twoPointLaw p := by
  rw [two_point_integral p hp hp1]
  have h0 := Real.sq_sqrt hp
  have h1 := Real.sq_sqrt (sub_nonneg.mpr hp1)
  calc
    _ = X 0*Y 0*(Real.sqrt p)^2+X 1*Y 1*(Real.sqrt (1-p))^2 := by ring
    _ = _ := by rw [h0,h1]; ring

theorem two_point_square_completion (p : ℝ) (X : Fin 2 → ℝ) (a : ℝ) :
    (X 0-a)^2*p+(X 1-a)^2*(1-p)=
      (a-(X 0*p+X 1*(1-p)))^2+(X 0-X 1)^2*p*(1-p) := by ring

/-- The unique closest constant is the actual expectation in the specified law. -/
theorem two_point_unique_minimum (p : ℝ) (hp : 0<p) (hp1 : p<1) (X : Fin 2 → ℝ) (a : ℝ) :
    (∫ w,(X w-(∫ z,X z ∂twoPointLaw p))^2 ∂twoPointLaw p) ≤
      (∫ w,(X w-a)^2 ∂twoPointLaw p) ∧
    ((∫ w,(X w-(∫ z,X z ∂twoPointLaw p))^2 ∂twoPointLaw p)=
      (∫ w,(X w-a)^2 ∂twoPointLaw p) ↔ a=∫ z,X z ∂twoPointLaw p) := by
  simp only [two_point_integral p hp.le hp1.le]
  have he b : p*(X 0-b)^2+(1-p)*(X 1-b)^2=
      (b-(p*X 0+(1-p)*X 1))^2+(X 0-X 1)^2*p*(1-p) := by ring
  rw [he,he]
  constructor
  · nlinarith [sq_nonneg (a-(p*X 0+(1-p)*X 1))]
  · constructor
    · intro h; nlinarith [sq_nonneg (a-(p*X 0+(1-p)*X 1))]
    · intro h; rw [h]

end Asakura.Chapter1Complete
