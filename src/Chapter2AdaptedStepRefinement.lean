import Chapter2AdaptedStepClipping

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem finite_endpoint_grid_contained {α : Type*} [LinearOrder α] (s : Finset α) (hs : s.Nonempty) :
    ∃ (N : ℕ) (u : ℕ → α), StrictMonoOn u (Iic N) ∧
      (∀ x ∈ s, ∃ k ≤ N, u k = x) ∧ (∀ k, u k ∈ s) := by
  classical
  let N := s.card-1
  have hpos : 0 < s.card := Finset.card_pos.2 hs
  have hcard : s.card = N+1 := by dsimp [N]; omega
  let e := s.orderEmbOfFin hcard
  let u := fun k => e ⟨min k N,by omega⟩
  refine ⟨N,u,?_,?_,?_⟩
  · intro i hi j hj hij
    change i ≤ N at hi
    change j ≤ N at hj
    apply e.strictMono
    change min i N < min j N
    simpa only [min_eq_left hi,min_eq_left hj] using hij
  · intro x hx
    have hx' : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨k,hk⟩ := hx'
    refine ⟨k.val,by omega,?_⟩
    simpa only [u,min_eq_left (show k.val ≤ N by omega)] using hk

  · intro k
    exact Finset.orderEmbOfFin_mem s hcard _

theorem finite_adapted_step_refinement
    {Ω α ι : Type*} [MeasurableSpace Ω] [LinearOrder α]
    (P : Measure Ω) (F : α → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (s : Finset ι) (a b : ι → α) (G : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hGm : ∀ i ∈ s, Measurable[F (a i)] (G i))
    (hGi : ∀ i ∈ s, MemLp (G i) ∞ P) (t0 : α) :
    ∃ (N : ℕ) (u : ℕ → α) (V : ℕ → Ω → ℝ),
      StrictMonoOn u (Iic N) ∧
      (∀ j, u j ∈ insert t0 (s.image a ∪ s.image b)) ∧
      (∀ j < N, Measurable[F (u j)] (V j) ∧ MemLp (V j) ∞ P) ∧
      ∀ ω t,
        (∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i ω) t) =
          ∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => V j ω) t := by
  classical
  let endpoints := insert t0 (s.image a ∪ s.image b)
  obtain ⟨N,u,hu,hmem,humem⟩ := finite_endpoint_grid_contained endpoints (Finset.insert_nonempty _ _)
  let U := fun j ω => ∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i ω) (u j)
  have hUm (j) : Measurable[F (u j)] (U j) := by
    apply Finset.measurable_sum
    intro i hi
    by_cases h : u j ∈ Ico (a i) (b i)
    · simp only [indicator_of_mem h]
      exact (hGm i hi).mono (hF h.1) le_rfl
    · simp only [indicator_of_notMem h]
      exact measurable_const
  have he (ω t) : (∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i ω) t) =
      ∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => U j ω) t := by
    have hei (i) (hi : i ∈ s) : (Ico (a i) (b i)).indicator (fun _ => G i ω) t =
        ∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator
          (fun _ => (Ico (a i) (b i)).indicator (fun _ => G i ω) (u j)) t := by
      obtain ⟨k,hk,hek⟩ := hmem (a i) (by simp only [endpoints,Finset.mem_insert,Finset.mem_union]; exact Or.inr (Or.inl (Finset.mem_image_of_mem a hi)))
      obtain ⟨l,hl,hel⟩ := hmem (b i) (by simp only [endpoints,Finset.mem_insert,Finset.mem_union]; exact Or.inr (Or.inr (Finset.mem_image_of_mem b hi)))
      have hkl : k ≤ l := (hu.le_iff_le hk hl).1 (by rw [hek,hel]; exact hab i hi)
      simpa only [hek,hel] using interval_step_refinement N u hu k l hk hl hkl (G i ω) t
    rw [Finset.sum_congr rfl hei,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases ht : t ∈ Ico (u j) (u (j+1))
    · simp only [indicator_of_mem ht,U]
    · simp only [indicator_of_notMem ht,Finset.sum_const_zero]
  refine ⟨N,u,U,hu,humem,?_,he⟩
  intro j hj
  refine ⟨hUm j,?_⟩
  apply memLp_finsetSum
  intro i hi
  by_cases h : u j ∈ Ico (a i) (b i)
  · simpa only [indicator_of_mem h] using hGi i hi
  · simp only [indicator_of_notMem h]
    exact MemLp.zero

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_endpoint_grid_contained
#print axioms Asakura.Chapter2Complete.finite_adapted_step_refinement
