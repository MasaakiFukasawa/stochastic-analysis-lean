import Chapter12AverageProductEdge

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def IgnoresCoordinate {e N : ℕ} (f : (Fin e → Fin (N+1)) → ℝ) (k : Fin e) : Prop :=
  ∀ a i,f (Function.update a k i)=f a

noncomputable def eliminateLastEdge {e N : ℕ} {V : Type*} [DecidableEq V]
    (f : V → (Fin (e+1) → Fin (N+1)) → ℝ) (p q : V)
    (v : V) (a : Fin e → Fin (N+1)) : ℝ :=
  eliminateEdgeFactor (fun w i => f w (Fin.snoc a i)) p q v

theorem ignores_last_coordinate {e N : ℕ}
    (f : (Fin (e+1) → Fin (N+1)) → ℝ) (h : IgnoresCoordinate f (Fin.last e))
    (a : Fin e → Fin (N+1)) (i : Fin (N+1)) : f (Fin.snoc a i)=f (Fin.snoc a 0) := by
  have hh := h (Fin.snoc a 0) i
  simpa only [Fin.update_snoc_last] using hh

theorem eliminated_ignores_coordinate {e N : ℕ} {V : Type*} [DecidableEq V]
    (f : V → (Fin (e+1) → Fin (N+1)) → ℝ) (p q v : V) (k : Fin e)
    (h : IgnoresCoordinate (f v) k.castSucc) :
    IgnoresCoordinate (eliminateLastEdge f p q v) k := by
  intro a i
  have he (j : Fin (N+1)) : f v (Fin.snoc (Function.update a k i) j)=f v (Fin.snoc a j) := by
    rw [Fin.snoc_update]
    exact h _ _
  unfold eliminateLastEdge eliminateEdgeFactor
  split_ifs
  · congr 1
    congr 1
    funext j
    dsimp only
    rw [he]
  · exact he 0

theorem eliminated_factor_nonnegative {e N : ℕ} {V : Type*} [DecidableEq V]
    (f : V → (Fin (e+1) → Fin (N+1)) → ℝ) (p q : V) (hf : ∀ v a,0≤f v a) :
    ∀ v a,0≤eliminateLastEdge f p q v a := by
  intro v a
  unfold eliminateLastEdge eliminateEdgeFactor
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact hf _ _

theorem eliminated_factor_square {e N : ℕ} {V : Type*} [DecidableEq V]
    (f : V → (Fin (e+1) → Fin (N+1)) → ℝ) (p q : V)
    (hdep : ∀ v,v≠p → v≠q → IgnoresCoordinate (f v) (Fin.last e)) (v : V) :
    cubeAverage N e (fun a => eliminateLastEdge f p q v a^2)=
      cubeAverage N (e+1) (fun a => f v a^2) := by
  change cubeAverage N e _=cubeAverage N e _
  congr 1
  funext a
  by_cases hv : v=p ∨ v=q
  · simp only [eliminateLastEdge,eliminateEdgeFactor,if_pos hv]
    exact Real.sq_sqrt (finiteAverage_nonneg _ (fun i => sq_nonneg _))
  · have hvp : v≠p := fun h => hv (Or.inl h)
    have hvq : v≠q := fun h => hv (Or.inr h)
    have he (i : Fin (N+1)) := ignores_last_coordinate (f v) (hdep v hvp hvq) a i
    simp only [eliminateLastEdge,eliminateEdgeFactor,if_neg hv]
    simp_rw [he]
    rw [finiteAverage_const]

end Asakura.Chapter12
