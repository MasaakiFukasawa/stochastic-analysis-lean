import Chapter12InverseHigherDerivative

open scoped ContDiff BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem inverse_all_higher_bounds {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (g : F → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f)
    (hb : ∀ k : ℕ,2≤k → ∃ C : ℝ,0≤C ∧ ∀x,‖iteratedFDeriv ℝ k f x‖≤C)
    (A : ℝ) (hA : 0≤A) (ha : ∀x,‖fderiv ℝ g x‖≤A) :
    ∀ k : ℕ,1≤k → ∃ C : ℝ,0≤C ∧ ∀x,‖iteratedFDeriv ℝ k g x‖≤C := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hk1 : k=1
    · subst k
      exact ⟨A,hA,fun x => by simpa only [norm_iteratedFDeriv_one] using ha x⟩
    have hk2 : 2≤k := by omega
    have hexB : ∀ j : ℕ,∃ C : ℝ,0≤C ∧ (2≤j → ∀x,‖iteratedFDeriv ℝ j f x‖≤C) := by
      intro j
      by_cases hj : 2≤j
      · obtain ⟨C,hC,h⟩ := hb j hj
        exact ⟨C,hC,fun _ => h⟩
      · exact ⟨0,le_rfl,fun h => (hj h).elim⟩
    have hexC : ∀ j : ℕ,∃ C : ℝ,0≤C ∧ (0<j → j<k → ∀x,‖iteratedFDeriv ℝ j g x‖≤C) := by
      intro j
      by_cases hj : 0<j ∧ j<k
      · obtain ⟨C,hC,h⟩ := ih j hj.2 hj.1
        exact ⟨C,hC,fun _ _ => h⟩
      · exact ⟨0,le_rfl,fun hp hlt => (hj ⟨hp,hlt⟩).elim⟩
    choose B hB hbB using hexB
    choose C hC hbC using hexC
    let R := ∑ c : OrderedFinpartition k with 2≤c.length,B c.length*∏ i,C (c.partSize i)
    have hR : 0≤R := Finset.sum_nonneg (fun c _ => mul_nonneg (hB _) (Finset.prod_nonneg (fun i _ => hC _)))
    refine ⟨A*R,mul_nonneg hA hR,?_⟩
    intro x
    apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hA hR)
    intro v
    obtain ⟨n,rfl⟩ : ∃n,k=n+2 := ⟨k-2,by omega⟩
    rw [inverse_higher_derivative_formula f g hf hg hl hr,norm_neg]
    have hh := higher_chain_remainder_bound g f (n+2) x B C hB hC
      (fun j hj _ => hbB j hj _) (fun j hj hlt => hbC j hj hlt _)
    calc
      ‖(fderiv ℝ g x) (higherChainRemainder g f (n+2) x v)‖
          ≤ A*‖higherChainRemainder g f (n+2) x v‖ :=
        ((fderiv ℝ g x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (ha x) (norm_nonneg _))
      _ ≤ A*(R*∏i,‖v i‖) := mul_le_mul_of_nonneg_left
        (((higherChainRemainder g f (n+2) x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right hh (Finset.prod_nonneg (fun i _ => norm_nonneg _)))) hA
      _ = (A*R)*∏i,‖v i‖ := (mul_assoc _ _ _).symm
end Asakura.Chapter12
#print axioms Asakura.Chapter12.inverse_all_higher_bounds
