import Chapter6UniformStepIntegral

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 2200000

lemma uniform_weighted_step_integral (R : ℝ) (hR : 0<R) (n : ℕ) (f g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 R) :
    (∫ r in Ioc 0 R,uniformLeftStep R n f r*g r)=
      ∑ k∈range (n+1),f ((k:ℝ)*(R/((n:ℝ)+1)))*
        ∫ r in (k:ℝ)*(R/((n:ℝ)+1))..((k:ℝ)+1)*(R/((n:ℝ)+1)),g r := by
  let h := R/((n:ℝ)+1)
  have hh : 0<h := div_pos hR (by positivity)
  have hend : ((n:ℝ)+1)*h=R := by dsimp [h]; field_simp
  have hsub k (hk : k∈range (n+1)) : Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)⊆Ioc 0 R := by
    apply Set.Ioc_subset_Ioc
    · positivity
    · have hk' : (k:ℝ)+1≤(n:ℝ)+1 := by exact_mod_cast mem_range.mp hk
      exact (mul_le_mul_of_nonneg_right hk' hh.le).trans_eq hend
  have hgi : IntegrableOn g (Ioc 0 R) volume := (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp hg
  have hi (k : ℕ) : IntegrableOn ((Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun r => f ((k:ℝ)*h)*g r)) (Ioc 0 R) volume :=
    (hgi.const_mul _).indicator measurableSet_Ioc
  have he r : uniformLeftStep R n f r*g r=
      ∑ k∈range (n+1),(Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun r => f ((k:ℝ)*h)*g r) r := by
    rw [uniformLeftStep,Finset.sum_mul]
    apply sum_congr rfl
    intro k _
    by_cases hr : r∈Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h) <;> simp [Set.indicator,hr,h]
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ => hi k)]
  apply sum_congr rfl
  intro k hk
  rw [setIntegral_indicator measurableSet_Ioc,inter_eq_self_of_subset_right (hsub k hk),integral_const_mul,
    intervalIntegral.integral_of_le (show (k:ℝ)*h≤((k:ℝ)+1)*h by nlinarith)]

end Asakura.Chapter6
