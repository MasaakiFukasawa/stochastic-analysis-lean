import Chapter12MultilinearArrayDifference
import Chapter12ArrayLinearBound

open scoped BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem multilinear_array_stability {m : ℕ} {J : Fin m → Type*} [∀i,Fintype (J i)]
    {E : Fin m → Type*} [∀i,NormedAddCommGroup (E i)] [∀i,NormedSpace ℝ (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A B : ContinuousMultilinearMap ℝ E F) (U V : ∀i,J i → E i)
    (C D : Fin m → ℝ) (hC : ∀i,0≤C i) (hD : ∀i,0≤D i)
    (hU : ∀i,Real.sqrt (∑j,‖U i j‖^2)≤C i)
    (hV : ∀i,Real.sqrt (∑j,‖V i j‖^2)≤C i)
    (hUV : ∀i,Real.sqrt (∑j,‖U i j-V i j‖^2)≤D i) :
    Real.sqrt (∑j : ∀i,J i,‖A (fun i => U i (j i))-B (fun i => V i (j i))‖^2)≤
      ‖A-B‖*∏i,C i+∑i,‖B‖*(D i*∏j∈Finset.univ.erase i,C j) := by
  classical
  have he (j : ∀i,J i) : A (fun i => U i (j i))-B (fun i => V i (j i))=
      (A-B) (fun i => U i (j i))+(B (fun i => U i (j i))-B (fun i => V i (j i))) := by
    simp only [ContinuousMultilinearMap.sub_apply]
    abel
  simp_rw [he]
  apply (array_add_norm_bound (fun j : ∀i,J i => (A-B) (fun i => U i (j i)))
    (fun j : ∀i,J i => B (fun i => U i (j i))-B (fun i => V i (j i)))).trans
  apply add_le_add
  · exact (multilinear_array_norm_bound (A-B) U).trans
      (mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => Real.sqrt_nonneg _) (fun i _ => hU i)) (norm_nonneg _))
  · exact multilinear_array_difference B U V C D hC hD hU hV hUV
end Asakura.Chapter12
#print axioms Asakura.Chapter12.multilinear_array_stability
