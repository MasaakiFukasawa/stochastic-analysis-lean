import Chapter2StepClipping

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Refining finitely many holding intervals and clipping the resulting
coefficients preserves their information constraints and essential boundedness.
The new partition is constructed from the old endpoints. -/
theorem finite_adapted_step_clipping
    {Ω α ι : Type*} [MeasurableSpace Ω] [LinearOrder α]
    (P : Measure Ω) (F : α → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (s : Finset ι) (a b : ι → α) (G : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hGm : ∀ i ∈ s, Measurable[F (a i)] (G i))
    (t0 : α) (L : ℝ) (hL : 0 ≤ L) :
    ∃ (N : ℕ) (u : ℕ → α) (V : ℕ → Ω → ℝ),
      StrictMonoOn u (Iic N) ∧
      (∀ j < N, Measurable[F (u j)] (V j) ∧ MemLp (V j) ∞ P) ∧
      ∀ ω t,
        max (-L) (min L (∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i ω) t)) =
          ∑ j ∈ Finset.range N, (Ico (u j) (u (j+1))).indicator (fun _ => V j ω) t := by
  classical
  let endpoints := insert t0 (s.image a ∪ s.image b)
  obtain ⟨N,u,hu,hmem⟩ := finite_endpoint_grid endpoints (Finset.insert_nonempty _ _)
  let U := fun j ω => ∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i ω) (u j)
  let V := fun j ω => max (-L) (min L (U j ω))
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
  refine ⟨N,u,V,hu,?_,?_⟩
  · intro j hj
    have hm : Measurable[F (u j)] (V j) := measurable_const.max (measurable_const.min (hUm j))
    refine ⟨hm,memLp_top_of_bound (hm.mono (hle _) le_rfl).aestronglyMeasurable L ?_⟩
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs]
    change |max (-L) (min L (U j ω))| ≤ L
    exact abs_le.2 ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
  · intro ω t
    rw [he ω t]
    exact grid_step_map N u hu (fun j => U j ω) (fun x => max (-L) (min L x))
      (by rw [min_eq_right hL,max_eq_right (by linarith)]) t

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_adapted_step_clipping
