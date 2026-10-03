import Chapter8GibbsCoordinateIBP

open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Asakura.Chapter8
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Integrate the diffusion generator against the Gibbs density. The
first derivatives Fⱼ and their derivatives DFⱼ are actual differentiable
functions, and all integral interchanges follow from the stated moment bound. -/
theorem gibbs_coordinate_generator_zero {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] [Fintype ι]
    (U : E → ℝ) (g : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hU : ∀ x, HasFDerivAt U (g x) x) (hg : Continuous g)
    (hi : Integrable (fun x : E => (1+‖x‖^2)*Real.exp (-β*U x)))
    (F : ι → E → ℝ) (DF : ι → E → E →L[ℝ] ℝ)
    (hDF : ∀ j, Continuous (DF j)) (hF : ∀ j x, HasFDerivAt (F j) (DF j x) x)
    (e : ι → E) (M : ι → ι → ℝ)
    (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ j x, |F j x| ≤ A)
    (hd : ∀ i j x, |DF j x (e i)| ≤ B)
    (hgrad : ∀ i x, |g x (e i)| ≤ C*(1+‖x‖)) :
    (∫ x : E, Real.exp (-β*U x)*
      (∑ i, ∑ j, M i j*(-g x (e i)*F j x+β⁻¹*DF j x (e i)))) = 0 := by
  let ρ := fun x => Real.exp (-β*U x)
  have hUc : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hU x).continuousAt)
  have hFc (j : ι) : Continuous (F j) :=
    continuous_iff_continuousAt.mpr (fun x => (hF j x).continuousAt)
  have hρ : Continuous ρ := by fun_prop
  have hρpos (x : E) : 0 ≤ ρ x := (Real.exp_pos _).le
  have hfb (j : ι) (x : E) : ‖F j x‖ ≤ A*(1+‖x‖^2) := by
    rw [Real.norm_eq_abs]
    nlinarith [hb j x,sq_nonneg ‖x‖]
  have hdb (i j : ι) (x : E) : ‖DF j x (e i)‖ ≤ B*(1+‖x‖^2) := by
    rw [Real.norm_eq_abs]
    nlinarith [hd i j x,sq_nonneg ‖x‖]
  have hpb (i j : ι) (x : E) : ‖g x (e i)*F j x‖ ≤ (2*C*A)*(1+‖x‖^2) := by
    rw [Real.norm_eq_abs,abs_mul]
    have hh := mul_le_mul (hgrad i x) (hb j x) (abs_nonneg _) (by positivity)
    have hn : 1+‖x‖ ≤ 2*(1+‖x‖^2) := by nlinarith [sq_nonneg (‖x‖-1)]
    have hh' := mul_le_mul_of_nonneg_left hn (mul_nonneg hC hA)
    nlinarith
  have hp (i j : ι) : Integrable (fun x => ρ x*(g x (e i)*F j x)) :=
    integrable_gibbs_polynomial_bound volume ρ _ hρpos hi
      (hρ.mul ((hg.clm_apply continuous_const).mul (hFc j))).aestronglyMeasurable _ (hpb i j)
  have hq (i j : ι) : Integrable (fun x => ρ x*DF j x (e i)) :=
    integrable_gibbs_polynomial_bound volume ρ _ hρpos hi
      (hρ.mul ((hDF j).clm_apply continuous_const)).aestronglyMeasurable _ (hdb i j)
  have hterm (i j : ι) : Integrable (fun x => ρ x*M i j*(-g x (e i)*F j x+β⁻¹*DF j x (e i))) := by
    convert ((hp i j).neg.add ((hq i j).const_mul β⁻¹)).const_mul (M i j) using 1
    funext x
    simp only [Pi.add_apply,Pi.neg_apply]
    ring
  have hz (i j : ι) : (∫ x, ρ x*M i j*(-g x (e i)*F j x+β⁻¹*DF j x (e i))) = 0 := by
    have hh := gibbs_coordinate_integration_by_parts U g β hU hg hi
      (F j) (DF j) (hDF j) (hF j) (e i) A B (2*C*A) (hfb j) (hdb i j) (hpb i j)
    have he : (fun x => ρ x*M i j*(-g x (e i)*F j x+β⁻¹*DF j x (e i))) =
        fun x => M i j*(-(ρ x*(g x (e i)*F j x))+β⁻¹*(ρ x*DF j x (e i))) := by
      funext x; ring
    rw [he,integral_const_mul,integral_add (f := fun x => -(ρ x*(g x (e i)*F j x))) (g := fun x => β⁻¹*(ρ x*DF j x (e i))) (hp i j).neg ((hq i j).const_mul β⁻¹),
      integral_neg,integral_const_mul]
    change M i j*(-(∫ x, ρ x*(g x (e i)*F j x))+β⁻¹*(∫ x, ρ x*DF j x (e i)))=0
    rw [hh]
    have he' : (∫ x, ρ x*g x (e i)*F j x) = ∫ x, ρ x*(g x (e i)*F j x) := by
      congr 1; funext x; ring
    rw [he',← mul_assoc,inv_mul_cancel₀ hβ,one_mul,neg_add_cancel,mul_zero]
  have he : (fun x : E => Real.exp (-β*U x)*
      (∑ i, ∑ j, M i j*(-g x (e i)*F j x+β⁻¹*DF j x (e i)))) =
      fun x => ∑ i, ∑ j, ρ x*M i j*(-g x (e i)*F j x+β⁻¹*DF j x (e i)) := by
    funext x
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [ρ]
    ring
  rw [he,integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hterm i j)]
  exact Finset.sum_eq_zero (fun j _ => hz i j)

end Asakura.Chapter8
