import Chapter7BlockAdaptedness
import Chapter7CenteredBlockVariance

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Variance bound for actual Brownian time blocks, including truncated cells. -/
theorem brownian_block_grid_variance {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (h : ℝ) (hh : 0 ≤ h) (ell : Fin n → ℝ)
    (hl0 : ∀ k,0 ≤ ell k) (hlh : ∀ k,ell k ≤ h) :
    let U := fun (k : Fin n) w => ∫ r in 0..ell k,
      (∑ j,u j*(B.W j (realTimeClamp ((k:ℝ)*h+r)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w))*
      (∑ j,v j*(B.W j (realTimeClamp ((k:ℝ)*h+r)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w))
    (∫ w,(∑ k,(U k w-(ell k)^2*(∑ j,u j*v j)/2))^2 ∂P) ≤
      (n:ℝ)*h^4*((∑ j,u j^2)*(∑ j,v j^2)+2*(∑ j,u j*v j)^2)/3 := by
  classical
  dsimp only
  let U := fun (k : Fin n) w => ∫ r in 0..ell k,
      (∑ j,u j*(B.W j (realTimeClamp ((k:ℝ)*h+r)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w))*
      (∑ j,v j*(B.W j (realTimeClamp ((k:ℝ)*h+r)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w))
  have hmom (k : Fin n) := shifted_brownian_block_moments P B u v ((k:ℝ)*h) (ell k)
    (mul_nonneg (by positivity) hh) (hl0 k)
  let F := fun k : Fin n => B.F (realTimeClamp ((k:ℝ)*h))
  have hpast (i j : Fin n) (hij : i < j) : StronglyMeasurable[F j] (U i) := by
    apply (brownian_block_adapted P B u v ((i:ℝ)*h) (ell i)
      (mul_nonneg (by positivity) hh) (hl0 i)).mono
    apply B.mono
    apply real_time_clamp_mono
    have hn : (i:ℝ)+1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hij)
    calc
      (i:ℝ)*h+ell i ≤ ((i:ℝ)+1)*h := by nlinarith [hlh i]
      _ ≤ (j:ℝ)*h := mul_le_mul_of_nonneg_right hn hh
  have he := centered_block_variance P U (fun k => (hmom k).1) F (fun k => B.le _) hpast
    (fun k => by simpa only [U,F,(hmom k).2.1] using (hmom k).2.2.2)
  have hmean k : (∫ w,U k w ∂P)=(ell k)^2*(∑ j,u j*v j)/2 := (hmom k).2.1
  simp only [hmean] at he
  rw [he]
  let L := (∑ j,u j^2)*(∑ j,v j^2)+2*(∑ j,u j*v j)^2
  have hL : 0 ≤ L := add_nonneg (mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by positivity)
  have hb k : (∫ w,(U k w-(ell k)^2*(∑ j,u j*v j)/2)^2 ∂P) ≤ h^4*L/3 := by
    have hd := mean_square_from_bias_variance P (U k) (hmom k).1 0
    simp only [sub_zero,hmean] at hd
    have hbound := (hmom k).2.2.1
    have hp : (ell k)^4 ≤ h^4 := pow_le_pow_left₀ (hl0 k) (hlh k) 4
    have hh' : (ell k)^4*L/3 ≤ h^4*L/3 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hL) (by norm_num)
    nlinarith [sq_nonneg ((ell k)^2*(∑ j,u j*v j)/2)]
  calc
    _ ≤ ∑ _k : Fin n,h^4*L/3 := Finset.sum_le_sum (fun k _ => hb k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,L]; ring

end Asakura.Chapter7
