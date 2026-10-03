import Chapter12GraphClosure
import Mathlib.Analysis.Normed.Lp.PiLp

open Set
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- A finite jet records the value and all derivatives together. Its
closure is a Banach space; closability ensures that the first coordinate
uniquely determines the other coordinates. -/
theorem closed_jet_value_injective {n : ℕ} (p : ℝ≥0∞) [Fact (1≤p)]
    (E : Fin (n+1) → Type*) [∀ j,NormedAddCommGroup (E j)] [∀ j,NormedSpace ℝ (E j)]
    (D : ∀ j : Fin n,E j.castSucc →ₗ.[ℝ] E j.succ)
    (G : Submodule ℝ (PiLp p E))
    (hG : ∀ x∈G,∀ j : Fin n,(x j.castSucc,x j.succ)∈(D j).graph) :
    Function.Injective (fun x : G => x.val 0) := by
  have hz (x : G) (hx : x.val 0=0) : x=0 := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    change x.val j=0
    induction j using Fin.induction with
    | zero => exact hx
    | succ j ih =>
      have hp := hG x.val x.property j
      rw [ih] at hp
      obtain ⟨y,hy,hy'⟩ := (D j).mem_graph_iff.mp hp
      have hye : y=0 := Subtype.ext hy
      rw [hye,LinearPMap.map_zero] at hy'
      exact hy'.symm
  intro x y hxy
  have he : (x-y : G).val 0=0 := by
    change x.val 0-y.val 0=0
    exact sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp (hz (x-y) he)

/-- Closed graphs pass derivative compatibility from smooth jets to their
joint closure; no separate choice of limits at different orders is made. -/
theorem closed_jet_compatibility {n : ℕ} (p : ℝ≥0∞) [Fact (1≤p)]
    (E : Fin (n+1) → Type*) [∀ j,NormedAddCommGroup (E j)] [∀ j,NormedSpace ℝ (E j)]
    (D : ∀ j : Fin n,E j.castSucc →ₗ.[ℝ] E j.succ) (hD : ∀ j,(D j).IsClosed)
    (G : Submodule ℝ (PiLp p E))
    (hG : ∀ x∈G,∀ j : Fin n,(x j.castSucc,x j.succ)∈(D j).graph) :
    ∀ x∈G.topologicalClosure,∀ j : Fin n,(x j.castSucc,x j.succ)∈(D j).graph := by
  intro x hx j
  let L : PiLp p E →L[ℝ] E j.castSucc × E j.succ :=
    (PiLp.proj p E j.castSucc).prod (PiLp.proj p E j.succ)
  have hc : IsClosed {x : PiLp p E | (x j.castSucc,x j.succ)∈(D j).graph} :=
    (hD j).preimage L.continuous
  exact closure_minimal (fun y hy => hG y hy j) hc hx

theorem sobolev_jet_closure_complete {n : ℕ} (p : ℝ≥0∞) [Fact (1≤p)]
    (E : Fin (n+1) → Type*) [∀ j,NormedAddCommGroup (E j)] [∀ j,NormedSpace ℝ (E j)]
    [∀ j,CompleteSpace (E j)] (G : Submodule ℝ (PiLp p E)) :
    CompleteSpace G.topologicalClosure :=
  G.isClosed_topologicalClosure.isComplete.completeSpace_coe

end Asakura.Chapter12
