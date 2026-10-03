import Appendix
open Set
namespace Asakura

/-- Ordered adjacent pairs in a d-dimensional integer grid with coordinates 0,...,N. -/
def GridEdge (d N : ℕ) :=
  {p : (Fin d → Fin (N+1)) × (Fin d → Fin (N+1)) //
    ∀ i, |((p.1 i).val : ℤ) - ((p.2 i).val : ℤ)| ≤ 1}

noncomputable instance (d N : ℕ) : Fintype (GridEdge d N) := by
  classical
  unfold GridEdge
  infer_instance

/-- Encode an edge by its first vertex and the three choices -1,0,1 in each coordinate. -/
def gridEdgeCode {d N : ℕ} (p : GridEdge d N) :
    (Fin d → Fin (N+1)) × (Fin d → Fin 3) :=
  (p.val.1, fun i => ⟨(((p.val.2 i).val : ℤ) - ((p.val.1 i).val : ℤ) + 1).toNat, by
    have h := (abs_le.mp (p.property i))
    omega⟩)

theorem gridEdgeCode_injective (d N : ℕ) :
    Function.Injective (@gridEdgeCode d N) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : (Fin d → Fin (N+1)) × (Fin d → Fin 3) => z.1) hpq
  · funext i
    apply Fin.ext
    have hfirst := congrArg (fun z => ((z.1 i).val : ℤ)) hpq
    have hsecond := congrArg (fun z => (z.2 i).val) hpq
    have hp := abs_le.mp (p.property i)
    have hq := abs_le.mp (q.property i)
    dsimp [gridEdgeCode] at hfirst hsecond
    omega

/-- C.2: the exact combinatorial bound used in the manuscript. -/
theorem grid_edge_cardinality (d N : ℕ) :
    Fintype.card (GridEdge d N) ≤ (N+1)^d * 3^d := by
  have h := Fintype.card_le_of_injective (@gridEdgeCode d N) (gridEdgeCode_injective d N)
  simpa using h

/-- C.2: specialize the edge count to the dyadic mesh. -/
theorem dyadic_grid_edge_cardinality (d m : ℕ) :
    Fintype.card (GridEdge d (2^m)) ≤ 2^(m*d) * 6^d := by
  apply (grid_edge_cardinality d (2^m)).trans
  have hpos : 0 < (2 : ℕ)^m := by positivity
  have hbase : (2 : ℕ)^m + 1 ≤ 2 * 2^m := by omega
  calc
    (2^m + 1)^d * 3^d ≤ (2 * 2^m)^d * 3^d :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase d)
    _ = 2^(m*d) * 6^d := by
      rw [mul_pow, ← pow_mul, show (6 : ℕ) = 2 * 3 from rfl, mul_pow]
      ring
end Asakura
