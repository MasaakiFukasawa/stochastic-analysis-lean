import Chapter12GraphAverageElimination

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

/-- A finite tensor network with two distinct endpoints per edge satisfies
a dimension-free product-of-L2-norms bound. The proof integrates one edge
at a time and applies Cauchy--Schwarz only to its two incident factors. -/
theorem finite_graph_holder (N e : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (left right : Fin e → V) (hneq : ∀ k,left k≠right k)
    (f : V → (Fin e → Fin (N+1)) → ℝ) (hf : ∀ v a,0≤f v a)
    (hdep : ∀ v k,v≠left k → v≠right k → IgnoresCoordinate (f v) k) :
    cubeAverage N e (fun a => ∏ v,f v a)≤
      ∏ v,Real.sqrt (cubeAverage N e (fun a => f v a^2)) := by
  induction e with
  | zero =>
    simp only [cubeAverage,Real.sqrt_sq_eq_abs]
    apply Finset.prod_le_prod₀ (fun v _ => hf v _) (fun v _ => ?_)
    exact le_abs_self _
  | succ e ih =>
    let p := left (Fin.last e)
    let q := right (Fin.last e)
    let g := eliminateLastEdge f p q
    have hg : ∀ v a,0≤g v a := eliminated_factor_nonnegative f p q hf
    have hlast : ∀ v,v≠p → v≠q → IgnoresCoordinate (f v) (Fin.last e) := fun v => hdep v (Fin.last e)
    have hgd : ∀ v k,v≠left k.castSucc → v≠right k.castSucc → IgnoresCoordinate (g v) k := by
      intro v k hvp hvq
      exact eliminated_ignores_coordinate f p q v k (hdep v k.castSucc hvp hvq)
    calc
      _=cubeAverage N e (fun a => finiteAverage (fun i => ∏ v,f v (Fin.snoc a i))) := rfl
      _≤cubeAverage N e (fun a => ∏ v,g v a) := by
        apply cubeAverage_mono
        intro a
        exact finiteAverage_product_edge (fun v i => f v (Fin.snoc a i)) p q (hneq (Fin.last e))
          (fun v i => hf v _) (fun v hvp hvq i => ignores_last_coordinate (f v) (hlast v hvp hvq) a i)
      _≤∏ v,Real.sqrt (cubeAverage N e (fun a => g v a^2)) :=
        ih (fun k => left k.castSucc) (fun k => right k.castSucc) (fun k => hneq k.castSucc) g hg hgd
      _=_ := by
        apply Finset.prod_congr rfl
        intro v _
        rw [eliminated_factor_square f p q hlast v]

end Asakura.Chapter12
