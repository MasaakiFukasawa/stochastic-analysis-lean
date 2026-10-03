import FullAuditHeatRemainder
import FullAuditCLTCancellation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.FullAudit

noncomputable def rowPast {n : ℕ} (k : Fin (n+1)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j.val < k.val)
noncomputable def rowFuture {n : ℕ} (k : Fin (n+1)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => k.val ≤ j.val)
noncomputable def rowSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (k : Fin (n+1)) (ω : Ω) : ℝ :=
  ∑ j ∈ rowPast k, X j ω
noncomputable def rowTime {n : ℕ} (v : Fin n → ℝ) (k : Fin (n+1)) : ℝ :=
  ∑ j ∈ rowFuture k, v j

theorem rowSum_succ {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (i : Fin n) (ω : Ω) :
    rowSum X i.succ ω = rowSum X i.castSucc ω + X i ω := by
  classical
  have he : rowPast i.succ = insert i (rowPast i.castSucc) := by
    ext j
    simp only [rowPast,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Fin.val_succ,Fin.val_castSucc]
    constructor
    · intro h
      by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr (by have hjv : j.val ≠ i.val := fun h => hji (Fin.ext h); omega)
    · rintro (rfl|h) <;> omega
  have hi : i ∉ rowPast i.castSucc := by simp [rowPast]
  simp only [rowSum,he,Finset.sum_insert hi]
  ring

theorem rowTime_succ {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    rowTime v i.castSucc = v i + rowTime v i.succ := by
  classical
  have he : rowFuture i.castSucc = insert i (rowFuture i.succ) := by
    ext j
    simp only [rowFuture,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Fin.val_succ,Fin.val_castSucc]
    constructor
    · intro h
      by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr (by have hjv : j.val ≠ i.val := fun h => hji (Fin.ext h); omega)
    · rintro (rfl|h) <;> omega
  have hi : i ∉ rowFuture i.succ := by simp [rowFuture]
  simp only [rowTime,he,Finset.sum_insert hi]

theorem rowTime_nonneg {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (k : Fin (n+1)) :
    0 ≤ rowTime v k := Finset.sum_nonneg fun i _ => hv i

theorem row_endpoints {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (v : Fin n → ℝ) :
    (∀ ω, rowSum X 0 ω = 0) ∧ (∀ ω, rowSum X (Fin.last n) ω = ∑ i, X i ω) ∧
      rowTime v 0 = ∑ i, v i ∧ rowTime v (Fin.last n) = 0 := by
  have hp0 : rowPast (0 : Fin (n+1)) = ∅ := by ext j; simp [rowPast]
  have hpn : rowPast (Fin.last n) = Finset.univ := by ext j; simp [rowPast,j.isLt]
  have hf0 : rowFuture (0 : Fin (n+1)) = Finset.univ := by ext j; simp [rowFuture]
  have hfn : rowFuture (Fin.last n) = ∅ := by ext j; simp [rowFuture,not_le.mpr j.isLt]
  simp [rowSum,rowTime,hp0,hpn,hf0,hfn]

theorem rowSum_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hmX : ∀ i, Measurable (X i)) (k : Fin (n+1)) : Measurable (rowSum X k) := by
  classical
  exact Finset.measurable_sum _ fun i _ => hmX i

/-- Independence of the new increment from the actual preceding partial sum. -/
theorem rowSum_independent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (i : Fin n) : IndepFun (X i) (rowSum X i.castSucc) P := by
  have hi : i ∉ rowPast i.castSucc := by simp [rowPast]
  have hh := hind.indepFun_finsetSum_of_notMem hmX hi
  have he : (∑ j ∈ rowPast i.castSucc, X j) = rowSum X i.castSucc := by
    funext ω
    simp only [Finset.sum_apply,rowSum]
  rw [he] at hh
  exact hh.symm

end Asakura.FullAudit
