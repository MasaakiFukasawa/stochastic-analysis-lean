import Chapter9AllOrderDomination
import Mathlib.Analysis.Normed.Group.Bounded

open Set Finset
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- On a compact subset of an open parameter domain, finitely many smooth
coefficient functions have a common bound for all derivatives up to order n. -/
theorem finite_coefficient_derivative_bounds {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : I → E → ℝ) (hf : ∀ j,ContDiffOn ℝ ∞ (f j) U) (n : ℕ) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ j i,i ≤ n → ∀ y∈K,
      ‖iteratedFDerivWithin ℝ i (f j) U y‖ ≤ B := by
  let H := fun y : E => fun j : I => fun i : Fin (n+1) =>
    ‖iteratedFDerivWithin ℝ i.val (f j) U y‖
  have hc : ContinuousOn H K := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro i
    exact ((hf j).continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hU.uniqueDiffOn).norm.mono hKU
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro j i hi y hy
  let k : Fin (n+1) := ⟨i,by omega⟩
  have h1 := norm_le_pi_norm (H y j) k
  have h2 := norm_le_pi_norm (H y) j
  have h3 := hB y hy
  have hh := h1.trans (h2.trans (h3.trans (le_max_right 0 B)))
  simpa only [H,k,Real.norm_eq_abs,abs_norm] using hh

/-- Differentiating a finite sum of polynomial weights times smooth
parameter coefficients preserves its polynomial growth in the data variable. -/
theorem weighted_coefficient_derivative_bound {E X I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : I → E → ℝ) (hf : ∀ j,ContDiffOn ℝ ∞ (f j) U)
    (w : I → X → ℝ) (r : X → ℝ)
    (hw : ∀ j x,|w j x| ≤ 1+(r x)^2) (n : ℕ) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ x y,y∈K → ∀ i,i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun z => ∑ j,w j x*f j z) U y‖ ≤ B*(1+(r x)^2) := by
  obtain ⟨B,hB,hbound⟩ := finite_coefficient_derivative_bounds U K hU hK hKU f hf n
  refine ⟨(Fintype.card I:ℝ)*B,by positivity,?_⟩
  intro x y hy i hi
  have hc j : ContDiffWithinAt ℝ i (f j) U y :=
    ((hf j).of_le (by exact_mod_cast le_top)) y (hKU hy)
  have hcw j (_ : j∈(univ : Finset I)) :
      ContDiffWithinAt ℝ i (fun z => w j x*f j z) U y := by
    simpa only [smul_eq_mul] using (hc j).const_smul (w j x)
  rw [iteratedFDerivWithin_fun_sum_apply hU.uniqueDiffOn (hKU hy) hcw]
  have he j : iteratedFDerivWithin ℝ i (fun z => w j x*f j z) U y=
      w j x • iteratedFDerivWithin ℝ i (f j) U y := by
    simpa only [Pi.smul_def,smul_eq_mul] using
      (iteratedFDerivWithin_const_smul_apply (a := w j x) (hc j) hU.uniqueDiffOn (hKU hy))
  simp_rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : I,(1+(r x)^2)*B := by
      apply sum_le_sum
      intro j _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hw j x) (hbound j i hi y hy) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring
end Asakura.Chapter9
