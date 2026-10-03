import Chapter6UniformStepIntegral

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem drift_grid_sum_identity {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (W V H : ℝ → Ω → ℝ) (β : Ω × ℝ → ℝ) (R : ℝ) (hR : 0<R)
    (hβi : ∀ w,IntervalIntegrable (fun r => β (w,r)) volume 0 R)
    (he : ∀ r,r∈Icc 0 R → W r=ᵐ[Q] fun w => V r w+∫ s in 0..r,β (w,s)) (n : ℕ) :
    (fun w => ∑ k∈range (n+1),H ((k:ℝ)*(R/(n+1))) w*
      (W (((k:ℝ)+1)*(R/(n+1))) w-W ((k:ℝ)*(R/(n+1))) w))=ᵐ[Q]
    (fun w => (∑ k∈range (n+1),H ((k:ℝ)*(R/(n+1))) w*
      (V (((k:ℝ)+1)*(R/(n+1))) w-V ((k:ℝ)*(R/(n+1))) w))+
      ∑ k∈range (n+1),H ((k:ℝ)*(R/(n+1))) w*
        ∫ r in (k:ℝ)*(R/(n+1))..((k:ℝ)+1)*(R/(n+1)),β (w,r)) := by
  let h := R/((n:ℝ)+1)
  have hh : 0<h := div_pos hR (by positivity)
  have hend : ((n:ℝ)+1)*h=R := by dsimp [h]; field_simp
  have htime (k : ℕ) (hk : k≤n+1) : (k:ℝ)*h∈Icc 0 R := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hh.le,?_⟩
    have hk' : (k:ℝ)≤(n:ℝ)+1 := by exact_mod_cast hk
    exact (mul_le_mul_of_nonneg_right hk' hh.le).trans_eq hend
  have hpair k (hk : k∈range (n+1)) : ∀ᵐ w ∂Q,
      W (((k:ℝ)+1)*h) w-W ((k:ℝ)*h) w=
        (V (((k:ℝ)+1)*h) w-V ((k:ℝ)*h) w)+∫ s in (k:ℝ)*h..((k:ℝ)+1)*h,β (w,s) := by
    have hka := htime k (mem_range.mp hk).le
    have hkb : ((k:ℝ)+1)*h∈Icc 0 R := by simpa only [Nat.cast_add,Nat.cast_one] using htime (k+1) (by have := mem_range.mp hk; omega)
    filter_upwards [he _ hka,he _ hkb] with w ha hb
    have hia : IntervalIntegrable (fun s => β (w,s)) volume 0 ((k:ℝ)*h) := (hβi w).mono_set (by simpa only [uIcc_of_le hR.le,uIcc_of_le hka.1] using Icc_subset_Icc_right hka.2)
    have hab : (k:ℝ)*h≤((k:ℝ)+1)*h := by nlinarith
    have hib : IntervalIntegrable (fun s => β (w,s)) volume ((k:ℝ)*h) (((k:ℝ)+1)*h) := (hβi w).mono_set (by simpa only [uIcc_of_le hR.le,uIcc_of_le hab] using Icc_subset_Icc hka.1 hkb.2)
    have hi := intervalIntegral.integral_add_adjacent_intervals hia hib
    rw [ha,hb]
    linarith
  filter_upwards [ae_all_iff.2 (fun k => ae_all_iff.2 (hpair k))] with w hw
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  change H ((k:ℝ)*h) w*(W (((k:ℝ)+1)*h) w-W ((k:ℝ)*h) w)=_
  rw [hw k hk]
  ring

end Asakura.Chapter6
