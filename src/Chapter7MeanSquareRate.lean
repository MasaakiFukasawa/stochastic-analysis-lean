import Chapter7MeanSquareProbability

open MeasureTheory Filter
open scoped Topology
namespace Asakura.Chapter7

lemma mean_square_rate_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (c A B : ℝ)
    (hi : ∀ n,MemLp (fun w => X n w-c) 2 P)
    (hb : ∀ n,(∫ w,(X n w-c)^2 ∂P) ≤ A/((n:ℝ)+1)+B/((n:ℝ)+1)^2) :
    TendstoInMeasure P X atTop (fun _ => c) := by
  apply mean_square_probability P X (fun _ => c) hi
  have ht : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlim := tendsto_inv_atTop_zero.comp ht
  have h1 : Tendsto (fun n : ℕ => A/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_zero,Function.comp_def] using hlim.const_mul A
  have h2 : Tendsto (fun n : ℕ => B/((n:ℝ)+1)^2) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,inv_pow,mul_zero,zero_pow (by decide : (2:ℕ)≠0),Function.comp_def] using (hlim.pow 2).const_mul B
  apply squeeze_zero (fun n => integral_nonneg (fun w => sq_nonneg _)) hb
  simpa only [zero_add] using h1.add h2

end Asakura.Chapter7
