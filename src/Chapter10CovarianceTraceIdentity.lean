import Chapter10QuadraticDriftBound
import Chapter10RiccatiTrace

open MeasureTheory Matrix
open scoped BigOperators
namespace Asakura.Chapter10
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The drift contribution to the covariance trace is exactly the expected
quadratic form; this connects the manuscript's sharp operator-norm estimate
to the actual second moments rather than a larger component norm. -/
theorem covariance_trace_contraction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (X : Ω → Fin d → ℝ) (hX : ∀ i,MemLp (fun w => X w i) 2 P)
    (A : Matrix (Fin d) (Fin d) ℝ) :
    (A*(show Matrix (Fin d) (Fin d) ℝ from fun i j => ∫ w,X w i*X w j ∂P)).trace=
      ∫ w,∑ i,X w i*(A*ᵥX w) i ∂P := by
  have hi i j : Integrable (fun w => A i j*(X w j*X w i)) P :=
    ((hX j).integrable_mul (hX i)).const_mul _
  have hsum i : (∑ j,A i j*(∫ w,X w j*X w i ∂P))=
      ∫ w,∑ j,A i j*(X w j*X w i) ∂P := by
    simp_rw [←integral_const_mul]
    exact (integral_finset_sum _ (fun j _ => hi i j)).symm
  change (∑ i,∑ j,A i j*(∫ w,X w j*X w i ∂P))=_
  simp_rw [hsum]
  rw [←integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Asakura.Chapter10
