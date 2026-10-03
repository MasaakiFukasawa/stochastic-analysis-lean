import Chapter2WrittenExtendedGrid
import Chapter1WrittenStopping

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter2Written
open Asakura.Chapter1Written

abbrev ClosedTime (T : EReal) := Icc (0 : EReal) T

noncomputable def gridTime {T : EReal} (n : ℕ) (t : ClosedTime T) : ClosedTime T :=
  ⟨extendedGrid T n t, (t.property.1.trans (extendedGrid_bounds t.property.1 t.property.2 n).1),
    (extendedGrid_bounds t.property.1 t.property.2 n).2⟩

theorem gridTime_finite_range (T : EReal) (n : ℕ) : (range (gridTime (T := T) n)).Finite := by
  let d := fun j : ℤ => (((j : ℝ)/(2 : ℝ)^n : ℝ) : EReal)
  have hD : (insert T (d '' Icc 0 ((n : ℤ)*2^n))).Finite := (finite_Icc _ _).image d |>.insert T
  have hv : (Subtype.val '' range (gridTime (T := T) n)).Finite := by
    apply hD.subset
    rintro z ⟨q, ⟨x, rfl⟩, rfl⟩
    rcases extendedGrid_range (T := T) x.property.1 n with h | ⟨j, hj0, hjn, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, ⟨hj0, hjn⟩, he.symm⟩
  exact hv.of_finite_image Subtype.val_injective.injOn

/-- A finite-valued time is stopping once its lower levels at its own grid points are. -/
theorem stopping_from_countable_grid {Ω ι : Type*} [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (τ : Ω → ι)
    (D : Set ι) (hD : D.Countable) (hr : ∀ ω, τ ω ∈ D)
    (hm : ∀ q ∈ D, MeasurableSet[F q] {ω | τ ω ≤ q}) :
    ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t} := by
  intro t
  have he : {ω | τ ω ≤ t} = ⋃ q ∈ D, ⋃ (_ : q ≤ t), {ω | τ ω ≤ q} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      exact ⟨τ ω, hr ω, h, le_rfl⟩
    · rintro ⟨q, hq, hqt, h⟩
      exact h.trans hqt
  rw [he]
  apply MeasurableSet.biUnion hD
  intro q hq
  apply MeasurableSet.iUnion
  intro hqt
  exact hF hqt _ (hm q hq)

/-- The repaired grid approximation is a stopping time for the original filtration
on [0,T], with T allowed to be ∞. No right-continuity of the filtration is assumed. -/
theorem gridTime_stopping {Ω : Type*} {T : EReal}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) (n : ℕ) :
    ∀ t, MeasurableSet[F t] {ω | gridTime n (τ ω) ≤ t} := by
  apply stopping_from_countable_grid F hF (fun ω => gridTime n (τ ω))
    (range (gridTime (T := T) n)) (gridTime_finite_range T n).countable
    (fun ω => mem_range_self (τ ω))
  intro q hq
  by_cases hqT : (q : EReal) = T
  · have he : {ω | gridTime n (τ ω) ≤ q} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      change (gridTime n (τ ω) : EReal) ≤ (q : EReal)
      rw [hqT]
      exact (gridTime n (τ ω)).property.2
    rw [he]
    exact MeasurableSet.univ
  · obtain ⟨x, hxq⟩ := hq
    have hg := extendedGrid_range (T := T) x.property.1 n
    have hxq' : extendedGrid T n x = (q : EReal) := congrArg Subtype.val hxq
    have hxq := hxq'
    rcases hg with h | ⟨j, hj0, hjn, hej⟩
    · exact (hqT (hxq.symm.trans h)).elim
    · have hqj : (q : EReal) = (((j : ℝ)/(2 : ℝ)^n : ℝ) : EReal) := hxq.symm.trans hej
      have hlt : (((j : ℝ)/(2 : ℝ)^n : ℝ) : EReal) < T := by
        rw [← hqj]
        exact lt_of_le_of_ne q.property.2 hqT
      have he : {ω | gridTime n (τ ω) ≤ q} = {ω | τ ω ≤ q} := by
        ext ω
        change extendedGrid T n (τ ω) ≤ (q : EReal) ↔ (τ ω : EReal) ≤ (q : EReal)
        rw [hqj]
        exact extendedGrid_le_grid T n (τ ω).property.1 j hjn hlt
      rw [he]
      exact hτ q

/-- Order of stopping times implies inclusion of the manuscript's stopped sigma algebras. -/
theorem written_stoppedSpace_mono {Ω ι : Type*} (m : MeasurableSpace Ω) [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (σ τ : Ω → ι)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) (hle : ∀ ω, σ ω ≤ τ ω) :
    writtenStoppedSpace m F σ hσ ≤ writtenStoppedSpace m F τ hτ := by
  intro A hA
  refine ⟨hA.1, fun t => ?_⟩
  have he : A ∩ {ω | τ ω ≤ t} = (A ∩ {ω | σ ω ≤ t}) ∩ {ω | τ ω ≤ t} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨⟨h.1, (hle ω).trans h.2⟩, h.2⟩
    · exact fun h => ⟨h.1.1, h.2⟩
  rw [he]
  exact (hA.2 t).inter (hτ t)

/-- Decreasing stopped sigma algebras, and the inclusion used after the backward limit. -/
theorem grid_stopped_sigmas {Ω : Type*} (m : MeasurableSpace Ω) {T : EReal}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) :
    Antitone (fun n => writtenStoppedSpace m F (fun ω => gridTime n (τ ω)) (gridTime_stopping F hF τ hτ n)) ∧
    writtenStoppedSpace m F τ hτ ≤
      ⨅ n, writtenStoppedSpace m F (fun ω => gridTime n (τ ω)) (gridTime_stopping F hF τ hτ n) := by
  constructor
  · intro i j hij
    apply written_stoppedSpace_mono
    intro ω
    exact extendedGrid_antitone T (τ ω) (τ ω).property.1 hij
  · apply le_iInf
    intro n
    apply written_stoppedSpace_mono
    intro ω
    exact (extendedGrid_bounds (τ ω).property.1 (τ ω).property.2 n).1

/-- The actual subtype-valued grid tends to the original time, including infinity. -/
theorem gridTime_tendsto {T : EReal} (t : ClosedTime T) :
    Tendsto (fun n => gridTime n t) atTop (𝓝 t) := by
  apply tendsto_subtype_rng.mpr
  exact extendedGrid_tendsto t.property.1 t.property.2

/-- The path limit uses right-continuity only, exactly as in the manuscript. -/
theorem gridTime_path_limit {T : EReal} (t : ClosedTime T)
    (X : ClosedTime T → ℝ) (hX : ContinuousWithinAt X (Ici t) t) :
    Tendsto (fun n => X (gridTime n t)) atTop (𝓝 (X t)) := by
  apply hX.tendsto.comp
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (gridTime_tendsto t)
  exact Eventually.of_forall (fun n => (extendedGrid_bounds t.property.1 t.property.2 n).1)

end Asakura.Chapter2Written
