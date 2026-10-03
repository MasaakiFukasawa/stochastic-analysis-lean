import FullAuditPartitionEnergy
import Chapter2WrittenGridStopping

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

noncomputable def qvPartition {T : EReal} [Fact (0 ≤ T)] (n j : ℕ) : ClosedTime T :=
  if hj : j ≤ n*2^n then
    ⟨min (((j:ℝ)/(2:ℝ)^n : ℝ):EReal) T,le_min (by positivity) Fact.out,min_le_right _ _⟩
  else ⊤

def qvPartitionLength (n : ℕ) : ℕ := n*2^n+1

theorem qv_partition_mono {T : EReal} [Fact (0 ≤ T)] (n : ℕ) :
    Monotone (qvPartition (T := T) n) := by
  intro j k hjk
  unfold qvPartition
  split_ifs with hj hk hk
  · change min _ T ≤ min _ T
    apply min_le_min_right
    apply EReal.coe_le_coe
    exact div_le_div_of_nonneg_right (by exact_mod_cast hjk) (by positivity)
  · exact le_top
  · exact False.elim (hj (hjk.trans hk))
  · exact le_rfl

theorem qv_partition_endpoints {T : EReal} [Fact (0 ≤ T)] (n : ℕ) :
    qvPartition (T := T) n 0 = ⊥ ∧ qvPartition (T := T) n (qvPartitionLength n) = ⊤ := by
  constructor
  · apply Subtype.ext
    simp [qvPartition,min_eq_left (Fact.out : 0 ≤ T)]
  · simp [qvPartition,qvPartitionLength]

/-- The finite grids in the printed quadratic-variation proof are nested. -/
theorem qv_partition_refinement {T : EReal} [Fact (0 ≤ T)] {n m : ℕ} (hnm : n ≤ m) :
    range (qvPartition (T := T) n) ⊆ range (qvPartition m) := by
  rintro t ⟨j,rfl⟩
  by_cases hj : j ≤ n*2^n
  · let k := j*2^(m-n)
    have he : (2:ℕ)^n*2^(m-n) = 2^m := by rw [← pow_add,Nat.add_sub_of_le hnm]
    have hk : k ≤ m*2^m := calc
      _ ≤ (n*2^n)*2^(m-n) := Nat.mul_le_mul_right _ hj
      _ = n*2^m := by rw [Nat.mul_assoc,he]
      _ ≤ m*2^m := Nat.mul_le_mul_right _ hnm
    refine ⟨k,?_⟩
    apply Subtype.ext
    simp only [qvPartition,dif_pos hk,dif_pos hj]
    congr 1
    apply congrArg (fun x : ℝ => (x:EReal))
    have heR : (2:ℝ)^n*2^(m-n) = 2^m := by exact_mod_cast he
    dsimp [k]
    push_cast
    rw [← heR]
    field_simp
  · refine ⟨qvPartitionLength m,?_⟩
    rw [(qv_partition_endpoints (T := T) m).2]
    simp [qvPartition,hj]

/-- The checked right-side grid approximation belongs to this exact finite
 partition, including the terminal point at infinity. -/
theorem grid_time_in_qv_partition {T : EReal} [Fact (0 ≤ T)] (n : ℕ) (t : ClosedTime T) :
    gridTime n t ∈ range (qvPartition n) := by
  obtain h | ⟨j,hj0,hjn,he⟩ := extendedGrid_range (T := T) t.property.1 n
  · refine ⟨qvPartitionLength n,?_⟩
    rw [(qv_partition_endpoints (T := T) n).2]
    apply Subtype.ext
    exact h.symm
  · have hj : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
    have hbound : j.toNat ≤ n*2^n := by exact_mod_cast (show (j.toNat:ℤ) ≤ (n:ℤ)*2^n by rwa [hj])
    refine ⟨j.toNat,?_⟩
    apply Subtype.ext
    simp only [qvPartition,dif_pos hbound,gridTime,Subtype.coe_mk]
    have hjR : (j.toNat:ℝ) = (j:ℝ) := by exact_mod_cast hj
    rw [hjR,← he,min_eq_left (extendedGrid_bounds t.property.1 t.property.2 n).2]

/-- At any two ordered partition points the square sum is increasing, even
 with repeated partition values. This is not asserted between grid points. -/
theorem partition_squares_mono_on_range {Ω ι : Type*} [LinearOrder ι] [OrderTop ι]
    (X : ι → Ω → ℝ) (π : ℕ → ι) (hπ : Monotone π) (N : ℕ) (hN : π N = ⊤) (ω : Ω) :
    MonotoneOn (fun t => partitionSquares X π N t ω) (range π) := by
  rintro s ⟨j,rfl⟩ t ⟨k,rfl⟩ hst
  let j0 := min j N
  let k0 := min k N
  have hj : π j0 = π j := by
    dsimp [j0]
    by_cases hj : j ≤ N
    · rw [min_eq_left hj]
    · rw [min_eq_right (le_of_not_ge hj),hN]
      exact (top_le_iff.mp (hN ▸ hπ (le_of_not_ge hj))).symm
  have hk : π k0 = π k := by
    dsimp [k0]
    by_cases hk : k ≤ N
    · rw [min_eq_left hk]
    · rw [min_eq_right (le_of_not_ge hk),hN]
      exact (top_le_iff.mp (hN ▸ hπ (le_of_not_ge hk))).symm
  change partitionSquares X π N (π j) ω ≤ partitionSquares X π N (π k) ω
  rw [← hj,← hk]
  by_cases h : j0 ≤ k0
  · rw [partition_squares_at_point X π hπ N j0 (min_le_right _ _) ω,
      partition_squares_at_point X π hπ N k0 (min_le_right _ _) ω]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun j _ _ => sq_nonneg _)
  · have he : π j0 = π k0 := le_antisymm (by simpa only [hj,hk] using hst) (hπ (le_of_not_ge h))
    rw [he]

end Asakura.FullAudit
