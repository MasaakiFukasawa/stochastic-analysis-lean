import Chapter12GaussianCommutatorTerms

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem ofFn_insertNth_eraseIdx {α : Type*} {k : ℕ}
    (i : Fin (k+1)) (a : α) (b : Fin k → α) :
    (List.ofFn (i.insertNth a b)).eraseIdx i.val=List.ofFn b := by
  induction k with
  | zero =>
    have hi : i=0 := by apply Fin.ext; omega
    subst i
    simp [List.ofFn_succ]
  | succ k ih =>
    refine Fin.cases ?_ (fun r => ?_) i
    · simp [List.ofFn_succ]
    · have hb : b=Fin.cons (b 0) (Fin.tail b) := (Fin.cons_self_tail b).symm
      rw [hb,Fin.insertNth_succ_cons,List.ofFn_succ]
      simp only [Fin.val_succ,List.eraseIdx_cons_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,Fin.val_succ]
      rw [ih]
      rw [List.ofFn_succ]
      simp

theorem ofFn_eraseIdx {α : Type*} {k : ℕ} (b : Fin (k+1) → α) (i : Fin (k+1)) :
    (List.ofFn b).eraseIdx i.val=List.ofFn (i.removeNth b) := by
  have hh := ofFn_insertNth_eraseIdx i (b i) (i.removeNth b)
  simpa only [Fin.insertNth_removeNth,Function.update_eq_self] using hh

end Asakura.Chapter12
