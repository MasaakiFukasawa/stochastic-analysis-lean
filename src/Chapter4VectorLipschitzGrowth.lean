import Chapter4VectorPaths

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.Chapter3Complete
set_option maxHeartbeats 1600000

lemma coordinate_lipschitz_growth
    {ι : Type*} [Fintype ι] {dim : ℕ} (b : ι → (Fin dim → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L) (h : ∀ i x y,(b i x-b i y)^2≤L*‖x-y‖^2) :
    ∃ K : ℝ,0≤K ∧ ∀ i x,(b i x)^2≤K*(1+∑ k,(x k)^2) := by
  classical
  let B := ∑ i,(b i 0)^2
  have hB : 0≤B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine ⟨2*L+2*B,by positivity,?_⟩
  intro i x
  have hb : (b i 0)^2≤B := Finset.single_le_sum (f := fun j => (b j 0)^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hx : ‖x‖^2≤∑ k,(x k)^2 := pi_norm_sq_le_sum_sq x
  have hh := h i x 0
  simp only [sub_zero] at hh
  have hsum : 0≤∑ k,(x k)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hscale := mul_le_mul_of_nonneg_left hx hL
  have hextra := mul_nonneg hB hsum
  nlinarith only [hh,hb,hscale,hextra,hL,sq_nonneg (b i x-2*b i 0)]

lemma vector_lipschitz_growth
    {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσ : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2) :
    ∃ K : ℝ,0≤K ∧ (∀ i x,(μ i x)^2≤K*(1+∑ k,(x k)^2)) ∧
      (∀ i j x,(σ i j x)^2≤K*(1+∑ k,(x k)^2)) := by
  obtain ⟨K₁,h₁,hμg⟩ := coordinate_lipschitz_growth μ L hL hμ
  obtain ⟨K₂,h₂,hσg⟩ := coordinate_lipschitz_growth (fun ij : Fin dim × Fin noise => σ ij.1 ij.2) L hL (fun ij => hσ ij.1 ij.2)
  refine ⟨K₁+K₂,add_nonneg h₁ h₂,?_,?_⟩
  · intro i x
    exact (hμg i x).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h₂)
      (add_nonneg zero_le_one (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
  · intro i j x
    exact (hσg (i,j) x).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h₁)
      (add_nonneg zero_le_one (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

end Asakura.Chapter4.Vector
