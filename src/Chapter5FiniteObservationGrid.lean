import Chapter5FiniteGridCentered

open Set
namespace Asakura.Chapter5
set_option maxHeartbeats 1600000

/-- A finite strictly increasing grid extends to a strictly increasing
real sequence; the artificial tail is never used in the stochastic argument. -/
theorem finite_strict_grid_extension (N : ℕ) (a : Fin (N+1) → ℝ) (ha : StrictMono a) :
    ∃ q : ℕ → ℝ,StrictMono q ∧ ∀ j : Fin (N+1),q j.val=a j := by
  let q := fun j => if h : j≤N then a ⟨j,by omega⟩ else a (Fin.last N)+(j-N:ℕ)
  refine ⟨q,?_,?_⟩
  · intro i j hij
    by_cases hi : i≤N
    · by_cases hj : j≤N
      · simpa only [q,dite_eq_left hi,dite_eq_left hj] using ha (show (⟨i,by omega⟩ : Fin (N+1))<⟨j,by omega⟩ from hij)
      · have hia : a ⟨i,by omega⟩≤a (Fin.last N) := ha.monotone (show (⟨i,by omega⟩ : Fin (N+1))≤Fin.last N from hi)
        have hpos : (0:ℝ)<(j-N:ℕ) := Nat.cast_pos.mpr (by omega)
        simp only [q,dite_eq_left hi,dite_eq_right hj]
        linarith
    · have hj : ¬j≤N := by omega
      have hsub : i-N<j-N := by omega
      simpa only [q,dite_eq_right hi,dite_eq_right hj,add_lt_add_iff_left,Nat.cast_lt] using hsub
  · intro j
    simp only [q,dite_eq_left (show j.val≤N by omega)]

theorem finite_observation_sorted_grid {k : ℕ}
    (τ : Fin k → ℝ) (hτ : ∀ i,0≤τ i) :
    ∃ N : ℕ,∃ q : ℕ → ℝ,∃ obs : Fin k → ℕ,
      StrictMono q ∧ q 0=0 ∧ (∀ i,obs i≤N) ∧ (∀ i,q (obs i)=τ i) ∧
      (q N=0 ∨ ∃ i,q N=τ i) := by
  classical
  let s := insert 0 (Finset.univ.image τ)
  have h0 : 0∈s := Finset.mem_insert_self _ _
  have hcard : s.card≠0 := Finset.card_ne_zero.mpr ⟨0,h0⟩
  obtain ⟨N,hN⟩ := Nat.exists_eq_succ_of_ne_zero hcard
  let e : Fin (N+1) ≃o s := s.orderIsoOfFin hN
  let a : Fin (N+1) → ℝ := fun j => (e j).val
  have ha : StrictMono a := fun _ _ hij => e.strictMono hij
  have hsmem (x : ℝ) (hx : x∈s) : x=0 ∨ ∃ i,x=τ i := by
    rcases Finset.mem_insert.mp hx with hx|hx
    · exact Or.inl hx
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact Or.inr ⟨i,rfl⟩
  have hapos (j : Fin (N+1)) : 0≤a j := by
    rcases hsmem _ (e j).property with hj|⟨i,hi⟩
    · exact le_of_eq hj.symm
    · change 0≤(e j).val
      rw [hi]
      exact hτ i
  have ha0 : a 0=0 := by
    apply le_antisymm _ (hapos 0)
    have hh := ha.monotone (show (0 : Fin (N+1))≤e.symm ⟨0,h0⟩ from Fin.zero_le _)
    simpa only [a,OrderIso.apply_symm_apply] using hh
  obtain ⟨q,hq,hqa⟩ := finite_strict_grid_extension N a ha
  let obs := fun i => (e.symm ⟨τ i,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩).val
  refine ⟨N,q,obs,hq,?_,?_,?_,?_⟩
  · exact (hqa 0).trans ha0
  · intro i
    exact Nat.le_of_lt_succ (e.symm ⟨τ i,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩).isLt
  · intro i
    simpa only [obs,a,OrderIso.apply_symm_apply] using hqa (e.symm ⟨τ i,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩)
  · rw [show q N=a (Fin.last N) from hqa (Fin.last N)]
    exact hsmem _ (e (Fin.last N)).property

end Asakura.Chapter5
