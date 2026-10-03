import Chapter10LinearCrossMoment
import Chapter4ConditionalCharacteristicLaw

open MeasureTheory Matrix
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.Chapter4
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Translate the operator used in the constructed SDE to the matrix
coordinates used by the manuscript. -/
theorem operator_cross_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (e : Ω → Fin d → ℝ)
    (he : ∀ i,MemLp (fun w => e w i) 2 P)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (i j : Fin d) :
    (∫ w,e w j*(A (e w)) i ∂P)=
      ∑ k,(A (Pi.single k 1)) i*(∫ w,e w k*e w j ∂P) := by
  let a : Matrix (Fin d) (Fin d) ℝ := fun i k => (A (Pi.single k 1)) i
  have hex w : (A (e w)) i=∑ k,a i k*e w k :=
    dual_coordinate_expansion ((ContinuousLinearMap.proj i).comp A) (e w)
  have hh := (linear_cross_moment P (fun i w => e w i) he a i j).2
  have hid w : e w j*(A (e w)) i=(∑ k,a i k*e w k)*e w j := by rw [hex,mul_comm]
  simpa only [hid] using hh

/-- The two drift contributions equal A V + V A-transpose entry by entry. -/
theorem operator_covariance_drift {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (e : Ω → Fin d → ℝ)
    (he : ∀ i,MemLp (fun w => e w i) 2 P)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (i j : Fin d) :
    let a : Matrix (Fin d) (Fin d) ℝ := fun i k => (A (Pi.single k 1)) i
    let V : Matrix (Fin d) (Fin d) ℝ := fun k l => ∫ w,e w k*e w l ∂P
    (∫ w,e w j*(A (e w)) i ∂P)+(∫ w,e w i*(A (e w)) j ∂P)=
      (a*V+V*a.transpose) i j := by
  dsimp only
  rw [operator_cross_moment P e he A i j,operator_cross_moment P e he A j i]
  simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm ((A (Pi.single k 1)) j)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => mul_comm _ _

end Asakura.Chapter10
