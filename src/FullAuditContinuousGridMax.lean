import FullAuditDoob
import FullAuditProgressive

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- Cumulative finite grids. Taking cumulative unions makes refinement explicit
 without assuming a separate set identity for the dyadic grids. -/
noncomputable def cumulativeGrid {T : EReal} (hT : 0 ≤ T) (n : ℕ) : Set (ClosedTime T) :=
  insert ⟨T,hT,le_rfl⟩ (⋃ k : Fin (n+1), range (gridTime (T := T) k.val))

theorem cumulative_grid_finite {T : EReal} (hT : 0 ≤ T) (n : ℕ) :
    (cumulativeGrid hT n).Finite := by
  exact (finite_iUnion fun k : Fin (n+1) => gridTime_finite_range T k.val).insert _

theorem cumulative_grid_mono {T : EReal} (hT : 0 ≤ T) : Monotone (cumulativeGrid hT) := by
  intro n m hnm t ht
  rcases ht with ht | ht
  · exact Or.inl ht
  · rcases mem_iUnion.mp ht with ⟨k,hk⟩
    exact Or.inr (mem_iUnion.mpr ⟨⟨k.val,lt_of_lt_of_le k.isLt (Nat.add_le_add_right hnm 1)⟩,hk⟩)

theorem grid_time_mem_cumulative {T : EReal} (hT : 0 ≤ T) (n : ℕ) (t : ClosedTime T) :
    gridTime n t ∈ cumulativeGrid hT n := by
  exact Or.inr (mem_iUnion.mpr ⟨⟨n,Nat.lt_succ_self n⟩,mem_range_self t⟩)

theorem cumulative_grid_nonempty {T : EReal} (hT : 0 ≤ T) (n : ℕ) :
    (cumulative_grid_finite hT n).toFinset.Nonempty := by
  exact ⟨⟨T,hT,le_rfl⟩,by simp [cumulativeGrid]⟩

noncomputable def cumulativeMax {Ω : Type*} {T : EReal} (hT : 0 ≤ T)
    (X : ClosedTime T → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (cumulative_grid_finite hT n).toFinset.sup'
    (cumulative_grid_nonempty hT n) (fun t => X t ω)

theorem cumulative_max_level {Ω : Type*} {T : EReal} (hT : 0 ≤ T)
    (X : ClosedTime T → Ω → ℝ) (n : ℕ) (ω : Ω) (a : ℝ) :
    a ≤ cumulativeMax hT X n ω ↔ ∃ t ∈ cumulativeGrid hT n, a ≤ X t ω := by
  classical
  unfold cumulativeMax
  rw [Finset.le_sup'_iff]
  simp only [Finite.mem_toFinset]

theorem cumulative_max_mono {Ω : Type*} {T : EReal} (hT : 0 ≤ T)
    (X : ClosedTime T → Ω → ℝ) (ω : Ω) : Monotone (fun n => cumulativeMax hT X n ω) := by
  intro n m hnm
  obtain ⟨t,ht,he⟩ := (cumulative_max_level hT X n ω (cumulativeMax hT X n ω)).mp le_rfl
  exact (cumulative_max_level hT X m ω _).mpr ⟨t,cumulative_grid_mono hT hnm ht,he⟩

theorem cumulative_max_measurable {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal}
    (hT : 0 ≤ T) (X : ClosedTime T → Ω → ℝ) (hX : ∀ t, Measurable[m] (X t)) (n : ℕ) :
    Measurable[m] (cumulativeMax hT X n) := by
  have h := Finset.measurable_sup' (s := (cumulative_grid_finite hT n).toFinset)
    (cumulative_grid_nonempty hT n) (fun t _ => hX t)
  have he : (cumulative_grid_finite hT n).toFinset.sup' (cumulative_grid_nonempty hT n) X = cumulativeMax hT X n := by
    funext ω
    exact Finset.sup'_apply _ _ _
  rwa [he] at h

/-- Right continuity identifies the supremum on all times with the limit of
 the actual finite-grid maxima, including infinite suprema. -/
theorem cumulative_max_supremum {Ω : Type*} {T : EReal} (hT : 0 ≤ T)
    (X : ClosedTime T → Ω → ℝ)
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t) (ω : Ω) :
    (⨆ n, ENNReal.ofReal (cumulativeMax hT X n ω)) = ⨆ t, ENNReal.ofReal (X t ω) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    obtain ⟨t,ht,he⟩ := (cumulative_max_level hT X n ω (cumulativeMax hT X n ω)).mp le_rfl
    exact (ENNReal.ofReal_le_ofReal he).trans (le_iSup (fun t => ENNReal.ofReal (X t ω)) t)
  · apply iSup_le
    intro t
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (gridTime_path_limit t (fun s => X s ω) (hr ω t))
    apply le_of_tendsto ht
    exact Eventually.of_forall fun n =>
      (ENNReal.ofReal_le_ofReal ((cumulative_max_level hT X n ω _).mpr
        ⟨gridTime n t,grid_time_mem_cumulative hT n t,le_rfl⟩)).trans
        (le_iSup (fun n => ENNReal.ofReal (cumulativeMax hT X n ω)) n)

/-- The finite-grid weak bound is obtained from the already checked finite
 Doob theorem, with the original terminal value included as the greatest time. -/
theorem cumulative_grid_weak {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ∀ t, Measurable[F t] (X t))
    (hY : Integrable (X ⟨T,hT,le_rfl⟩) P) (hpos : ∀ t, 0 ≤ᵐ[P] X t)
    (hdom : ∀ t, X t ≤ᵐ[P] P[X ⟨T,hT,le_rfl⟩ | F t])
    (n : ℕ) (a : ℝ) (ha : 0 < a) :
    P.real {ω | a ≤ cumulativeMax hT X n ω} ≤
      a⁻¹ * ∫ ω in {ω | a ≤ cumulativeMax hT X n ω}, X ⟨T,hT,le_rfl⟩ ω ∂P := by
  classical
  let D := cumulativeGrid hT n
  letI : Fintype D := (cumulative_grid_finite hT n).fintype
  letI : OrderTop D := { top := ⟨⟨T,hT,le_rfl⟩,Or.inl rfl⟩, le_top := fun t => t.val.property.2 }
  have h := doob_weak_written P (fun t : D => F t) (fun _ _ h => hF h) (fun t => hle t)
    (fun t : D => X t) (fun t => hX t) hY (fun t => hpos t) (fun t => hdom t) a ha
  have he : {ω | ∃ t : D, a ≤ X t.val ω} = {ω | a ≤ cumulativeMax hT X n ω} := by
    ext ω
    change (∃ t : D, a ≤ X t.val ω) ↔ a ≤ cumulativeMax hT X n ω
    rw [cumulative_max_level]
    constructor
    · rintro ⟨t,ht⟩; exact ⟨t.val,t.property,ht⟩
    · rintro ⟨t,ht,hx⟩; exact ⟨⟨t,ht⟩,hx⟩
  change P.real {ω | ∃ t : D, a ≤ X t.val ω} ≤ a⁻¹ *
    ∫ ω in {ω | ∃ t : D, a ≤ X t.val ω}, X ⟨T,hT,le_rfl⟩ ω ∂P at h
  rwa [he] at h

end Asakura.FullAudit
