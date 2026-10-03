import Chapter2StepRefinement

open Set
open scoped Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- A zero elementary integrand gives zero gain, for every price path.
The proof refines all intervals onto a grid and uses the actual values
of the integrand on that grid. -/
theorem finite_step_zero_gain {α ι : Type*} [LinearOrder α]
    (s : Finset ι) (a b : ι → α) (hab : ∀ i ∈ s, a i ≤ b i)
    (G : ι → ℝ) (X : α → ℝ) (t : α)
    (hzero : ∀ r, (∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i) r) = 0) :
    (∑ i ∈ s, G i * (X (min (b i) t)-X (min (a i) t))) = 0 := by
  obtain ⟨N,u,_,he⟩ := finite_step_common_grid s a b hab t
  rw [he G X t]
  simp only [hzero,zero_mul,Finset.sum_const_zero]

/-- Independence of the finite holding-interval representation in the
definition of the elementary Ito integral, before taking any limits. -/
theorem elementary_integral_representation_independent
    {α ι κ : Type*} [LinearOrder α]
    (s : Finset ι) (r : Finset κ) (a b : ι → α) (c d : κ → α)
    (hab : ∀ i ∈ s, a i ≤ b i) (hcd : ∀ j ∈ r, c j ≤ d j)
    (G : ι → ℝ) (J : κ → ℝ)
    (heq : ∀ v,
      (∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i) v) =
      ∑ j ∈ r, (Ico (c j) (d j)).indicator (fun _ => J j) v)
    (X : α → ℝ) (t : α) :
    (∑ i ∈ s, G i * (X (min (b i) t)-X (min (a i) t))) =
    ∑ j ∈ r, J j * (X (min (d j) t)-X (min (c j) t)) := by
  classical
  have h := finite_step_zero_gain (s.disjSum r) (Sum.elim a c) (Sum.elim b d)
    (by intro i hi; cases i with
        | inl i => exact hab i (by simpa using hi)
        | inr j => exact hcd j (by simpa using hi))
    (Sum.elim G (fun j => -J j)) X t
  have hz : ∀ v, (∑ i ∈ s.disjSum r,
      (Ico (Sum.elim a c i) (Sum.elim b d i)).indicator
        (fun _ => Sum.elim G (fun j => -J j) i) v) = 0 := by
    intro v
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl,Sum.elim_inr]
    have hn (j) : (Ico (c j) (d j)).indicator (fun _ => -J j) v =
        -(Ico (c j) (d j)).indicator (fun _ => J j) v := by
      by_cases hv : v ∈ Ico (c j) (d j) <;> simp [hv]
    simp only [hn,Finset.sum_neg_distrib,heq v,add_neg_cancel]
  specialize h hz
  simp only [Finset.sum_disjSum,Sum.elim_inl,Sum.elim_inr,neg_mul,Finset.sum_neg_distrib] at h
  exact sub_eq_zero.1 (by simpa only [sub_eq_add_neg] using h)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_step_zero_gain
#print axioms Asakura.Chapter2Complete.elementary_integral_representation_independent
