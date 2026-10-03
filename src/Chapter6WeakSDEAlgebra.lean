import Chapter6LinearCoefficientBound

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1500000

lemma weak_sde_matrix_algebra {d : ℕ} (S A : Fin d → Fin d → ℝ)
    (hSA : ∀ i k,∑ j,S i j*A j k = if i=k then 1 else 0)
    (g : Fin d → ℝ → ℝ) (r : ℝ)
    (hi : ∀ k,IntervalIntegrable (g k) volume 0 r)
    (ξ W V : Fin d → ℝ)
    (hV : ∀ j,V j = W j-∫ s in 0..r,∑ k,A j k*g k s) :
    ∀ i,ξ i+∑ j,S i j*W j = ξ i+(∫ s in 0..r,g i s)+∑ j,S i j*V j := by
  intro i
  have hsum j : IntervalIntegrable (fun s => ∑ k,A j k*g k s) volume 0 r := by
    convert IntervalIntegrable.sum Finset.univ (fun k _ => (hi k).const_mul (A j k)) using 1
    ext s
    simp
  have hd : (∑ j,S i j*(∫ s in 0..r,∑ k,A j k*g k s)) = ∫ s in 0..r,g i s := by
    simp_rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finsetSum (fun j _ => (hsum j).const_mul (S i j))]
    congr 1
    funext s
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc,← Finset.sum_mul,hSA]
    simp
  simp_rw [hV,mul_sub,Finset.sum_sub_distrib]
  linarith

end Asakura.Chapter6
