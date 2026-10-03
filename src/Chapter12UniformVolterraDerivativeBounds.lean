import Chapter12VolterraDerivativeArrayBound

open MeasureTheory Set
open scoped Topology ContDiff NNReal BigOperators
namespace Asakura.Chapter12
universe u v w
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem uniform_volterra_derivative_bounds {E : Type u} {α : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : α → Type u) (N : α → Type w)
    [∀a,NormedAddCommGroup (G a)] [∀a,NormedSpace ℝ (G a)] [∀a,Fintype (N a)]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T)
    (Q X : ∀a,G a → C(Icc (0:ℝ) T,E))
    (hQ : ∀a,ContDiff ℝ ∞ (Q a)) (hX : ∀a,ContDiff ℝ ∞ (X a))
    (heq : ∀a z t,X a z t=Q a z t+∫s in 0..t.val,b (X a z (projIcc 0 T hT s)))
    (e : ∀a,N a → G a) (B : ℕ → ℝ) (hB : ∀k,0≤B k)
    (hQB : ∀k:ℕ,1≤k → ∀a z t,
      Real.sqrt (∑i : Fin k → N a,‖(iteratedFDeriv ℝ k (Q a) z (e a ∘ i)) t‖^2)≤B k) :
    ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀a z t,
      Real.sqrt (∑i : Fin k → N a,‖(iteratedFDeriv ℝ k (X a) z (e a ∘ i)) t‖^2)≤C := by
  classical
  obtain ⟨L,hL⟩ := hbound 1 le_rfl
  have hDb x : ‖fderiv ℝ b x‖≤(L:ℝ) := by simpa only [norm_iteratedFDeriv_one] using hL x
  have hexD : ∀j:ℕ,∃C:ℝ,0≤C ∧ (1≤j → ∀x,‖iteratedFDeriv ℝ j b x‖≤C) := by
    intro j
    by_cases hj : 1≤j
    · obtain ⟨C,hC⟩ := hbound j hj
      exact ⟨C,C.coe_nonneg,fun _ => hC⟩
    · exact ⟨0,le_rfl,fun h => (hj h).elim⟩
  choose D hD hbD using hexD
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hexC : ∀j:ℕ,∃C:ℝ,0≤C ∧ (0<j → j<k → ∀a z t,
        Real.sqrt (∑i : Fin j → N a,‖(iteratedFDeriv ℝ j (X a) z (e a ∘ i)) t‖^2)≤C) := by
      intro j
      by_cases hj : 0<j ∧ j<k
      · obtain ⟨C,hC,h⟩ := ih j hj.2 hj.1
        exact ⟨C,hC,fun _ _ => h⟩
      · exact ⟨0,le_rfl,fun hp hlt => (hj ⟨hp,hlt⟩).elim⟩
    choose C hC hbC using hexC
    let R := ∑c : OrderedFinpartition k with 2≤c.length,D c.length*∏i,C (c.partSize i)
    have hR : 0≤R := Finset.sum_nonneg (fun c _ => mul_nonneg (hD _) (Finset.prod_nonneg (fun i _ => hC _)))
    refine ⟨(B k+T*R)*Real.exp (((L:ℝ)+1)*T),mul_nonneg (add_nonneg (hB k) (mul_nonneg hT hR)) (Real.exp_pos _).le,?_⟩
    intro a z t
    obtain ⟨n,rfl⟩ : ∃n,k=n+1 := ⟨k-1,by omega⟩
    exact volterra_derivative_array_bound b hb hbound T hT (Q a) (X a) (hQ a) (hX a) (heq a)
      n z (e a) L (B (n+1)) L.coe_nonneg (hB _) hDb D C hD hC
      (fun j hj _ => hbD j (by omega)) (hQB (n+1) (by omega) a z)
      (fun j hj hlt => hbC j hj hlt a z) t
end Asakura.Chapter12
#print axioms Asakura.Chapter12.uniform_volterra_derivative_bounds
