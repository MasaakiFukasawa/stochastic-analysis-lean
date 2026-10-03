import Chapter6UniformStepLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 2200000

lemma uniform_left_step_integral (R : ℝ) (hR : 0<R) (n : ℕ) (f : ℝ → ℝ) :
    (∫ r in Ioc 0 R,uniformLeftStep R n f r)=
      ∑ k∈range (n+1),(R/((n:ℝ)+1))*f ((k:ℝ)*(R/((n:ℝ)+1))) := by
  let h := R/((n:ℝ)+1)
  have hh : 0<h := div_pos hR (by positivity)
  have hend : ((n:ℝ)+1)*h=R := by dsimp [h]; field_simp
  have hsub k (hk : k∈range (n+1)) : Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)⊆Ioc 0 R := by
    apply Set.Ioc_subset_Ioc
    · positivity
    · have hk' : (k:ℝ)+1≤(n:ℝ)+1 := by exact_mod_cast mem_range.mp hk
      exact (mul_le_mul_of_nonneg_right hk' hh.le).trans_eq hend
  have hi (k : ℕ) : IntegrableOn ((Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => f ((k:ℝ)*h))) (Ioc 0 R) volume :=
    (integrable_const _).indicator measurableSet_Ioc
  change (∫ r in Ioc 0 R,∑ k∈range (n+1),(Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => f ((k:ℝ)*h)) r)=_
  rw [integral_finsetSum _ (fun k _ => hi k)]
  apply sum_congr rfl
  intro k hk
  rw [setIntegral_indicator measurableSet_Ioc,inter_eq_self_of_subset_right (hsub k hk)]
  simp only [setIntegral_const,smul_eq_mul,Real.volume_real_Ioc]
  rw [show ((k:ℝ)+1)*h-(k:ℝ)*h=h by ring,max_eq_left hh.le]

end Asakura.Chapter6
