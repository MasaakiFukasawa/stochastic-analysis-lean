import Chapter12ClosedSobolevJets

open Set
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The completion of smooth jets remains a graph over the function value.
All derivative orders are completed simultaneously in the finite Lp sum norm. -/
theorem sobolev_jet_completion {n : ℕ} {ι : Type*} (p : ℝ≥0∞) [Fact (1≤p)]
    (E : Fin (n+1) → Type*) [∀ j,NormedAddCommGroup (E j)] [∀ j,NormedSpace ℝ (E j)]
    [∀ j,CompleteSpace (E j)]
    (D : ∀ j : Fin n,E j.castSucc →ₗ.[ℝ] E j.succ) (hD : ∀ j,(D j).IsClosed)
    (jet : ι → PiLp p E)
    (hjet : ∀ c j,(jet c j.castSucc,jet c j.succ)∈(D j).graph) :
    let G := (Submodule.span ℝ (range jet)).topologicalClosure
    CompleteSpace G ∧ Function.Injective (fun x : G => x.val 0) ∧
      ∀ x : G,∀ j : Fin n,(x.val j.castSucc,x.val j.succ)∈(D j).graph := by
  let V := Submodule.span ℝ (range jet)
  have hV : ∀ x∈V,∀ j : Fin n,(x j.castSucc,x j.succ)∈(D j).graph := by
    intro x hx j
    let L : PiLp p E →L[ℝ] E j.castSucc × E j.succ :=
      (PiLp.proj p E j.castSucc).prod (PiLp.proj p E j.succ)
    have hs : V≤(D j).graph.comap L.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨c,rfl⟩
      exact hjet c j
    exact hs hx
  have hc := closed_jet_compatibility p E D hD V hV
  exact ⟨sobolev_jet_closure_complete p E V,
    closed_jet_value_injective p E D V.topologicalClosure hc,
    fun x j => hc x.val x.property j⟩

end Asakura.Chapter12
