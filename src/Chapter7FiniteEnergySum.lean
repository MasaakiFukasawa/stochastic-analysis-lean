import Chapter7OrthogonalSquareSum
import Chapter7DriftRemainderAlgebra

open MeasureTheory Finset
open scoped BigOperators
namespace Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false

/-- A finite sum needs no independence for this energy bound. -/
lemma finite_energy_sum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 P) :
    (∫ w,(∑ i,X i w)^2 ∂P) ≤ (n:ℝ)*∑ i,∫ w,(X i w)^2 ∂P := by
  have hi i : Integrable (fun w => X i w^2) P :=
    (memLp_two_iff_integrable_sq (hX i).aestronglyMeasurable).mp (hX i)
  have hs : MemLp (fun w => ∑ i,X i w) 2 P := memLp_finsetSum _ (fun i _ => hX i)
  have his : Integrable (fun w => (∑ i,X i w)^2) P :=
    (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp hs
  calc
    _ ≤ ∫ w,(n:ℝ)*∑ i,X i w^2 ∂P := by
      apply integral_mono his ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _)
      intro w
      have he := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
        (f := fun _ : Fin n => (1:ℝ)) (g := fun i => X i w)
      simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using he
    _ = _ := by rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]

end Asakura.Chapter7
