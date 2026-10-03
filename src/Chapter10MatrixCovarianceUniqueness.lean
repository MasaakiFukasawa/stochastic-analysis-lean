import Chapter10CovarianceODEUniqueness
import Mathlib.Analysis.Matrix.Normed

open Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma elementwise_matrix_product_bound {d : ℕ} (A D : Matrix (Fin d) (Fin d) ℝ) :
    ‖A*D‖≤(d:ℝ)*‖A‖*‖D‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  simp only [Matrix.mul_apply]
  calc
    _ ≤ ∑ k,‖A i k*D k j‖ := norm_sum_le _ _
    _ ≤ ∑ k,‖A‖*‖D‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (A i) k).trans (norm_le_pi_norm A i))
        ((norm_le_pi_norm (D k) j).trans (norm_le_pi_norm D k)) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/-- Entrywise matrix version of covariance uniqueness, with the same norm
and derivatives as the constructed second-moment matrix. -/
theorem matrix_covariance_unique {d : ℕ}
    (V S a b q : ℝ → Matrix (Fin d) (Fin d) ℝ) (T C : ℝ) (hC : 0≤C)
    (hV : ContinuousOn V (Icc 0 T)) (hS : ContinuousOn S (Icc 0 T))
    (hdV : ∀ t∈Ico 0 T,HasDerivWithinAt V (a t*V t+V t*b t+q t) (Ici t) t)
    (hdS : ∀ t∈Ico 0 T,HasDerivWithinAt S (a t*S t+S t*b t+q t) (Ici t) t)
    (ha : ∀ t∈Ico 0 T,‖a t‖≤C) (hb : ∀ t∈Ico 0 T,‖b t‖≤C)
    (hzero : V 0=S 0) : ∀ t∈Icc 0 T,V t=S t := by
  have he := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun t => V t-S t)
    (f' := fun t => a t*V t+V t*b t+q t-(a t*S t+S t*b t+q t))
    (K := 2*d*C) (a := 0) (b := T) (hV.sub hS)
    (fun t ht => (hdV t ht).sub (hdS t ht)) (sub_eq_zero.mpr hzero) (by
      intro t ht
      have hid : a t*V t+V t*b t+q t-(a t*S t+S t*b t+q t)=
          a t*(V t-S t)+(V t-S t)*b t := by noncomm_ring
      rw [hid]
      have hl := elementwise_matrix_product_bound (a t) (V t-S t)
      have hr := elementwise_matrix_product_bound (V t-S t) (b t)
      have ha' : (d:ℝ)*‖a t‖*‖V t-S t‖≤(d:ℝ)*C*‖V t-S t‖ := by gcongr; exact ha t ht
      have hb' : (d:ℝ)*‖V t-S t‖*‖b t‖≤(d:ℝ)*‖V t-S t‖*C := by gcongr; exact hb t ht
      have hn := norm_add_le (a t*(V t-S t)) ((V t-S t)*b t)
      nlinarith)
  exact fun t ht => sub_eq_zero.mp (he t ht)

end Asakura.Chapter10
