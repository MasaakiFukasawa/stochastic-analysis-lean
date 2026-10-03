import Chapter4VectorGlobalExistence

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
set_option maxHeartbeats 1500000

lemma coordinate_continuous_of_square_lipschitz {dim : ℕ}
    (b : (Fin dim → ℝ) → ℝ) (L : ℝ) (hL : 0≤L)
    (hb : ∀ x y,(b x-b y)^2≤L*‖x-y‖^2) : Continuous b := by
  have hh : LipschitzWith ⟨Real.sqrt L,Real.sqrt_nonneg L⟩ b := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm]
    change ‖b x-b y‖≤Real.sqrt L*‖x-y‖
    have h := hb x y
    have he : (Real.sqrt L*‖x-y‖)^2=L*‖x-y‖^2 := by rw [mul_pow,Real.sq_sqrt hL]
    have hn : 0≤Real.sqrt L*‖x-y‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs]
    nlinarith only [h,he,hn,sq_abs (b x-b y),abs_nonneg (b x-b y)]
  exact hh.continuous

/-- The manuscript's sum-of-squares Lipschitz assumption implies the
coordinate bounds in the sup norm used by the finite-dimensional Lean space. -/
theorem manuscript_lipschitz_coordinates {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L)
    (h : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2) :
    (∀ i,Continuous (μ i)) ∧ (∀ i j,Continuous (σ i j)) ∧
    (∀ i x y,(μ i x-μ i y)^2≤(L*(dim:ℝ))*‖x-y‖^2) ∧
    (∀ i j x y,(σ i j x-σ i j y)^2≤(L*(dim:ℝ))*‖x-y‖^2) := by
  classical
  have hx (x y : Fin dim → ℝ) : (∑ i,(x i-y i)^2)≤(dim:ℝ)*‖x-y‖^2 := by
    calc
      _ ≤ ∑ i : Fin dim,‖x-y‖^2 := Finset.sum_le_sum (fun i _ => by
        have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (x-y) i) 2
        simpa only [Pi.sub_apply,Real.norm_eq_abs,sq_abs] using hh)
      _ = _ := by simp
  have hm i x y : (μ i x-μ i y)^2≤(L*(dim:ℝ))*‖x-y‖^2 := by
    have hsingle := Finset.single_le_sum (s := Finset.univ) (f := fun i => (μ i x-μ i y)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hs : 0≤∑ i,∑ j,(σ i j x-σ i j y)^2 := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hf := (h x y).trans (mul_le_mul_of_nonneg_left (hx x y) hL)
    nlinarith only [hsingle,hs,hf]
  have hs i j x y : (σ i j x-σ i j y)^2≤(L*(dim:ℝ))*‖x-y‖^2 := by
    have hsingle := Finset.single_le_sum (s := Finset.univ) (f := fun j => (σ i j x-σ i j y)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ j)
    have hrow := Finset.single_le_sum (s := Finset.univ) (f := fun i => ∑ j,(σ i j x-σ i j y)^2)
      (fun i _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
    have hp : 0≤∑ i,(μ i x-μ i y)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hf := (h x y).trans (mul_le_mul_of_nonneg_left (hx x y) hL)
    nlinarith only [hsingle,hrow,hp,hf]
  exact ⟨fun i => coordinate_continuous_of_square_lipschitz (μ i) _ (by positivity) (hm i),
    fun i j => coordinate_continuous_of_square_lipschitz (σ i j) _ (by positivity) (hs i j),hm,hs⟩

end Asakura.Chapter4.Vector
