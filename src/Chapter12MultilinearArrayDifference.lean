import Chapter12MultilinearArrayBound
import Chapter12BanachArrayNorm

open scoped BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 240000
set_option backward.isDefEq.respectTransparency false

theorem multilinear_array_difference {m : ℕ} {J : Fin m → Type*} [∀i,Fintype (J i)]
    {E : Fin m → Type*} [∀i,NormedAddCommGroup (E i)] [∀i,NormedSpace ℝ (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ContinuousMultilinearMap ℝ E F) (U V : ∀i,J i → E i)
    (C D : Fin m → ℝ) (hC : ∀i,0≤C i) (hD : ∀i,0≤D i)
    (hU : ∀i,Real.sqrt (∑j,‖U i j‖^2)≤C i)
    (hV : ∀i,Real.sqrt (∑j,‖V i j‖^2)≤C i)
    (hUV : ∀i,Real.sqrt (∑j,‖U i j-V i j‖^2)≤D i) :
    Real.sqrt (∑j : ∀i,J i,‖A (fun i => U i (j i))-A (fun i => V i (j i))‖^2)≤
      ∑i,‖A‖*(D i*∏j∈Finset.univ.erase i,C j) := by
  classical
  let M := fun (i j : Fin m) (a : J j) => if j < i then U j a else if i = j then U j a-V j a else V j a
  have he (a : ∀i,J i) : A (fun i => U i (a i))-A (fun i => V i (a i))=
      ∑i,A (fun j => M i j (a j)) := by
    simpa only [Finset.piecewise_univ,Finset.mem_univ,true_implies,M,ContinuousMultilinearMap.coe_coe] using
      A.toMultilinearMap.map_sub_map_piecewise (fun i => U i (a i)) (fun i => V i (a i)) Finset.univ
  simp_rw [he]
  apply (banach_array_norm_sum (I:=(∀i,J i)) (J:=Fin m) (E:=F) (fun (i : Fin m) (a : ∀j,J j) => A (fun j => M i j (a j)))).trans
  apply Finset.sum_le_sum
  intro i _
  apply (multilinear_array_norm_bound A (M i)).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hMi j : Real.sqrt (∑a,‖M i j a‖^2)≤(if i = j then D j else C j) := by
    by_cases hji : j < i
    · simp only [M,hji,if_true,if_neg (ne_of_gt hji)]
      exact hU j
    · by_cases hij : i = j
      · simp only [M,hji,if_false,hij,if_true,lt_self_iff_false]
        exact hUV j
      · simp only [M,hji,if_false,hij]
        exact hV j
  calc
    _ ≤ ∏j,if i = j then D j else C j :=
      Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) (fun j _ => hMi j)
    _ = D i*∏j∈Finset.univ.erase i,C j := by
      rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [if_pos rfl]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      exact if_neg (Finset.mem_erase.mp hj).1.symm
end Asakura.Chapter12
#print axioms Asakura.Chapter12.multilinear_array_difference
