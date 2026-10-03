import Chapter7DriftBrownianCross
import Chapter7DriftSquareGridBound

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma drift_square_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (b c : ℝ → Ω → ℝ) (T K : ℝ)
    (hT : 0<T) (hK : 0≤K)
    (hb : ∀ r∈Icc 0 T,∀ w,|b r w|≤K) (hc : ∀ r∈Icc 0 T,∀ w,|c r w|≤K) :
    TendstoInMeasure P (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*∑ k : Fin (n+1),
      (∫ r in (k:ℝ)*(T/(n+1))..((k:ℝ)+1)*(T/(n+1)),b r w)*
      (∫ r in (k:ℝ)*(T/(n+1))..((k:ℝ)+1)*(T/(n+1)),c r w)) atTop (fun _ => 0) := by
  let h := fun n : ℕ => T/((n:ℝ)+1)
  let A := fun n (k : Fin (n+1)) w => ∫ r in (k:ℝ)*h n..((k:ℝ)+1)*h n,b r w
  let C := fun n (k : Fin (n+1)) w => ∫ r in (k:ℝ)*h n..((k:ℝ)+1)*h n,c r w
  have hbound n (k : Fin (n+1)) (g : ℝ → Ω → ℝ) (hg : ∀ r∈Icc 0 T,∀ w,|g r w|≤K) w :
      |∫ r in (k:ℝ)*h n..((k:ℝ)+1)*h n,g r w|≤K*h n := by
    have hh : 0≤h n := by dsimp [h]; positivity
    have hleft := (grid_left_in_interval T hT.le n k).1
    have hright : ((k:ℝ)+1)*h n≤T := by
      have hk : (k:ℝ)+1≤(n:ℝ)+1 := by exact_mod_cast (Nat.succ_le_of_lt k.isLt)
      calc
        _ ≤ ((n:ℝ)+1)*h n := mul_le_mul_of_nonneg_right hk hh
        _ = T := by dsimp [h]; field_simp
    have hstep : ((k:ℝ)+1)*h n-(k:ℝ)*h n=h n := by ring
    have he := bounded_drift_increment (fun r => g r w) ((k:ℝ)*h n) (((k:ℝ)+1)*h n) K
      (by nlinarith) (fun r hr => hg r ⟨hleft.trans hr.1,hr.2.trans hright⟩ w)
    simpa only [hstep] using he
  let D := fun n : ℕ => K^2*T^2/Real.sqrt ((n+1:ℕ):ℝ)
  have hd : Tendsto D atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hi := Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_inv_atTop_zero.comp hn)
    simpa only [D,Function.comp_def,Real.sqrt_inv,Real.sqrt_zero,div_eq_mul_inv,mul_zero] using hi.const_mul (K^2*T^2)
  have hp : TendstoInMeasure P (fun n (_ : Ω) => D n) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all P (fun _ => hd))
  apply probability_of_abs_le P _ _ hp
  intro n
  apply ae_of_all
  intro w
  have he := drift_square_grid_bound (Nat.succ_pos n) (fun k => A n k w) (fun k => C n k w) T K hT.le hK
    (fun k => by simpa only [A,C,h,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using hbound n k b hb w)
    (fun k => by simpa only [A,C,h,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using hbound n k c hc w)
  simpa only [A,C,h,D,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (by positivity : 0≤K^2*T^2/Real.sqrt ((n+1:ℕ):ℝ))] using he

end Asakura.Chapter7
