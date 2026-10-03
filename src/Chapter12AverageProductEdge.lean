import Chapter12FiniteAverages

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

private theorem prod_two_factors {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (p q : V) (hpq : p≠q) :
    (∏ v,f v)=f p*f q*(∏ v∈(Finset.univ.erase p).erase q,f v) := by
  have hq : q∈(Finset.univ.erase p) := Finset.mem_erase.mpr ⟨hpq.symm,Finset.mem_univ _⟩
  calc
    _=f p*(∏ v∈Finset.univ.erase p,f v) := (Finset.mul_prod_erase _ _ (Finset.mem_univ p)).symm
    _=f p*(f q*(∏ v∈(Finset.univ.erase p).erase q,f v)) := by rw [Finset.mul_prod_erase _ _ hq]
    _=_ := by ring

noncomputable def eliminateEdgeFactor {N : ℕ} {V : Type*} [DecidableEq V]
    (f : V → Fin (N+1) → ℝ) (p q v : V) : ℝ :=
  if v=p ∨ v=q then Real.sqrt (finiteAverage (fun i => f v i^2)) else f v 0

/-- Average over one edge. Only its two endpoints vary in that coordinate,
so a single Cauchy--Schwarz inequality controls the whole tensor product. -/
theorem finiteAverage_product_edge {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → Fin (N+1) → ℝ) (p q : V) (hpq : p≠q)
    (hf : ∀ v i,0≤f v i) (hconst : ∀ v,v≠p → v≠q → ∀ i,f v i=f v 0) :
    finiteAverage (fun i => ∏ v,f v i)≤∏ v,eliminateEdgeFactor f p q v := by
  let C := ∏ v∈(Finset.univ.erase p).erase q,f v 0
  have hC : 0≤C := Finset.prod_nonneg (fun v _ => hf v 0)
  have hrest (i : Fin (N+1)) : (∏ v∈(Finset.univ.erase p).erase q,f v i)=C := by
    apply Finset.prod_congr rfl
    intro v hv
    exact hconst v (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1 (Finset.mem_erase.mp hv).1 i
  have he (i : Fin (N+1)) : (∏ v,f v i)=f p i*f q i*C := by
    rw [prod_two_factors _ p q hpq,hrest]
  have hg : (∏ v,eliminateEdgeFactor f p q v)=
      Real.sqrt (finiteAverage (fun i => f p i^2))*
        Real.sqrt (finiteAverage (fun i => f q i^2))*C := by
    rw [prod_two_factors _ p q hpq]
    simp only [eliminateEdgeFactor,eq_self_iff_true,true_or,or_true,if_true]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    have hvp := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
    have hvq := (Finset.mem_erase.mp hv).1
    simp [hvp,hvq]
  simp_rw [he]
  rw [finiteAverage_mul_const,hg]
  exact mul_le_mul_of_nonneg_right (finiteAverage_cauchy_schwarz (f p) (f q)) hC

end Asakura.Chapter12
