import Chapter12VolterraDerivativeArrayStability

open MeasureTheory Set
open scoped Topology ContDiff NNReal BigOperators
namespace Asakura.Chapter12
universe u v w
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem uniform_volterra_derivative_stability {E : Type u} {α : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : α → Type u) (N : α → Type w)
    [∀a,NormedAddCommGroup (G a)] [∀a,NormedSpace ℝ (G a)] [∀a,Fintype (N a)]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T)
    (Q Q' X Y : ∀a,G a → C(Icc (0:ℝ) T,E))
    (hQ : ∀a,ContDiff ℝ ∞ (Q a)) (hQ' : ∀a,ContDiff ℝ ∞ (Q' a))
    (hX : ∀a,ContDiff ℝ ∞ (X a)) (hY : ∀a,ContDiff ℝ ∞ (Y a))
    (heX : ∀a z t,X a z t=Q a z t+∫s in 0..t.val,b (X a z (projIcc 0 T hT s)))
    (heY : ∀a z t,Y a z t=Q' a z t+∫s in 0..t.val,b (Y a z (projIcc 0 T hT s)))
    (e : ∀a,N a → G a) (B C : ℕ → ℝ) (hB : ∀k,0≤B k) (hC : ∀k,0≤C k)
    (ε : ∀a,G a → ℝ) (hε : ∀a z,0≤ε a z)
    (hXY : ∀a z t,‖X a z t-Y a z t‖≤ε a z)
    (hQD : ∀k:ℕ,1≤k → ∀a z t,Real.sqrt (∑i : Fin k → N a,
      ‖(iteratedFDeriv ℝ k (Q a) z (e a ∘ i)) t-(iteratedFDeriv ℝ k (Q' a) z (e a ∘ i)) t‖^2)≤B k*ε a z)
    (hXC : ∀k:ℕ,1≤k → ∀a z t,Real.sqrt (∑i : Fin k → N a,
      ‖(iteratedFDeriv ℝ k (X a) z (e a ∘ i)) t‖^2)≤C k)
    (hYC : ∀k:ℕ,1≤k → ∀a z t,Real.sqrt (∑i : Fin k → N a,
      ‖(iteratedFDeriv ℝ k (Y a) z (e a ∘ i)) t‖^2)≤C k) :
    ∀k:ℕ,1≤k → ∃K:ℝ,0≤K ∧ ∀a z t,Real.sqrt (∑i : Fin k → N a,
      ‖(iteratedFDeriv ℝ k (X a) z (e a ∘ i)) t-(iteratedFDeriv ℝ k (Y a) z (e a ∘ i)) t‖^2)≤K*ε a z := by
  classical
  have hexD : ∀j:ℕ,∃D:ℝ,0≤D ∧ (1≤j → ∀x,‖iteratedFDeriv ℝ j b x‖≤D) := by
    intro j
    by_cases hj : 1≤j
    · obtain ⟨D,hD⟩ := hbound j hj
      exact ⟨D,D.coe_nonneg,fun _ => hD⟩
    · exact ⟨0,le_rfl,fun h => (hj h).elim⟩
  choose D hD hbD using hexD
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hexJ : ∀j:ℕ,∃K:ℝ,0≤K ∧ (0<j → j<k → ∀a z t,Real.sqrt (∑i : Fin j → N a,
        ‖(iteratedFDeriv ℝ j (X a) z (e a ∘ i)) t-(iteratedFDeriv ℝ j (Y a) z (e a ∘ i)) t‖^2)≤K*ε a z) := by
      intro j
      by_cases hj : 0<j ∧ j<k
      · obtain ⟨K,hK,h⟩ := ih j hj.2 hj.1
        exact ⟨K,hK,fun _ _ => h⟩
      · exact ⟨0,le_rfl,fun hp hlt => (hj ⟨hp,hlt⟩).elim⟩
    choose J hJ hbJ using hexJ
    let R := ∑c : OrderedFinpartition k with 2≤c.length,
      (D (c.length+1)*(∏i,C (c.partSize i))+
        ∑i,D c.length*(J (c.partSize i)*∏j∈Finset.univ.erase i,C (c.partSize j)))
    have hR : 0≤R := Finset.sum_nonneg (fun c _ => add_nonneg
      (mul_nonneg (hD _) (Finset.prod_nonneg (fun i _ => hC _)))
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hD _) (mul_nonneg (hJ _) (Finset.prod_nonneg (fun j _ => hC _))))))
    refine ⟨(B k+T*(D 2*C k+R))*Real.exp ((D 1+1)*T),?_,?_⟩
    · exact mul_nonneg (add_nonneg (hB _) (mul_nonneg hT (add_nonneg (mul_nonneg (hD _) (hC _)) hR))) (Real.exp_pos _).le
    · intro a z t
      obtain ⟨n,rfl⟩ : ∃n,k=n+1 := ⟨k-1,by omega⟩
      have hh := volterra_derivative_array_stability b hb hbound T hT (Q a) (Q' a) (X a) (Y a)
        (hQ a) (hQ' a) (hX a) (hY a) (heX a) (heY a) n z (e a) D C J hD hC hJ hbD
        (B (n+1)) (ε a z) (hB _) (hε a z) (hXY a z) (hQD _ hk a z)
        (fun j hj _ => hXC j hj a z) (fun j hj _ => hYC j hj a z) (fun j hj hlt => hbJ j hj hlt a z) t
      convert hh using 1 <;> dsimp only [R] <;> ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.uniform_volterra_derivative_stability
