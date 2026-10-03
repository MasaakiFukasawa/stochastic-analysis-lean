import Chapter7BrownianSecondMoments
import Chapter7PredictableDriftBound
import Chapter7MeanSquareRate

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma predictable_drift_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (T K : ℝ) (hT : 0<T) (hK : 0≤K)
    (b : (n : ℕ) → Fin (n+1) → Ω → ℝ)
    (ha : ∀ (n : ℕ) (k : Fin (n+1)),Measurable[B.F (realTimeClamp ((k:ℝ)*(T/(n+1))))] (b n k))
    (hb : ∀ n k w,|b n k w|≤K) :
    TendstoInMeasure P (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*∑ k : Fin (n+1),
      (T/(n+1))*b n k w*(∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*(T/(n+1)))) w-
        B.W j (realTimeClamp ((k:ℝ)*(T/(n+1)))) w))) atTop (fun _ => 0) := by
  let h := fun n : ℕ => T/((n+1:ℕ):ℝ)
  let Z := fun n (k : Fin (n+1)) w => ∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*h n)) w-
    B.W j (realTimeClamp ((k:ℝ)*h n)) w)
  have hh n : 0≤h n := div_nonneg hT.le (Nat.cast_nonneg _)
  have hz n (k : Fin (n+1)) : MemLp (Z n k) 2 P :=
    (brownian_projection_second P B ((k:ℝ)*h n) (((k:ℝ)+1)*h n)
      (mul_nonneg (by positivity) (hh n)) (by nlinarith [hh n]) u).1
  have hbi n k : MemLp (b n k) ⊤ P := MemLp.of_bound
    ((ha n k).mono (B.le _) le_rfl).aestronglyMeasurable K
      (ae_of_all P (fun w => by simpa only [Real.norm_eq_abs] using hb n k w))
  have hi n : MemLp (fun w => ∑ k : Fin (n+1),(h n)*b n k w*Z n k w) 2 P := by
    apply memLp_finsetSum
    intro k _
    simpa only [Pi.mul_apply,mul_assoc] using ((hbi n k).mul (hz n k)).const_mul (h n)
  apply mean_square_rate_probability P _ 0 (K^2*(∑ j,u j^2)*T^3) 0
  · intro n
    simpa only [h,Z,Nat.cast_add,Nat.cast_one,sub_zero] using (hi n).const_mul (Real.sqrt ((n+1:ℕ):ℝ))
  · intro n
    simp only [sub_zero,zero_div,add_zero]
    have he := predictable_drift_bound P B u (h n) (hh n) (b n)
      (fun k => by
        have heh : h n=T/((n:ℝ)+1) := by simp only [h,Nat.cast_add,Nat.cast_one]
        rw [heh]
        exact ha n k) K hK (hb n)
    have hnR : 0<((n+1:ℕ):ℝ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left he hnR.le
    have hid : (∫ w,(Real.sqrt ((n+1:ℕ):ℝ)*(∑ k : Fin (n+1),h n*b n k w*Z n k w))^2 ∂P)=
        ((n+1:ℕ):ℝ)*(∫ w,(∑ k : Fin (n+1),h n*b n k w*Z n k w)^2 ∂P) := by
      simp only [mul_pow,Real.sq_sqrt hnR.le,integral_const_mul]
    have hncast : (n:ℝ)+1=((n+1:ℕ):ℝ) := by norm_num
    rw [hncast]
    change (∫ w,(Real.sqrt ((n+1:ℕ):ℝ)*(∑ k : Fin (n+1),h n*b n k w*Z n k w))^2 ∂P)≤_
    rw [hid]
    apply hscaled.trans_eq
    dsimp only [h]
    push_cast
    field_simp
    <;> ring

end Asakura.Chapter7
