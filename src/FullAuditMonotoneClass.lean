import ManuscriptPiLambda

open Set MeasureTheory
namespace Asakura.FullAudit

structure WrittenMonotone {Ω : Type*} (L : Set (Set Ω)) : Prop where
  increasing : ∀ f : ℕ → Set Ω, (∀ n, f n ∈ L) → Monotone f → (⋃ n, f n) ∈ L
  decreasing : ∀ f : ℕ → Set Ω, (∀ n, f n ∈ L) → Antitone f → (⋂ n, f n) ∈ L

def monotoneHull {Ω : Type*} (A : Set (Set Ω)) : Set (Set Ω) :=
  {E | ∀ L, WrittenMonotone L → A ⊆ L → E ∈ L}

theorem monotoneHull_closed {Ω : Type*} (A : Set (Set Ω)) :
    WrittenMonotone (monotoneHull A) := by
  constructor
  · intro f hf hm L hL hAL
    exact hL.increasing f (fun n => hf n L hL hAL) hm
  · intro f hf hm L hL hAL
    exact hL.decreasing f (fun n => hf n L hL hAL) hm

theorem monotone_complement_class {Ω : Type*} (L : Set (Set Ω))
    (hL : WrittenMonotone L) : WrittenMonotone {E | Eᶜ ∈ L} := by
  constructor
  · intro f hf hm
    change (⋃ n, f n)ᶜ ∈ L
    rw [Set.compl_iUnion]
    exact hL.decreasing _ hf (fun n m hnm => compl_subset_compl.mpr (hm hnm))
  · intro f hf hm
    change (⋂ n, f n)ᶜ ∈ L
    rw [Set.compl_iInter]
    exact hL.increasing _ hf (fun n m hnm => compl_subset_compl.mpr (hm hnm))

theorem monotone_intersection_class {Ω : Type*} (L : Set (Set Ω))
    (hL : WrittenMonotone L) (E : Set Ω) : WrittenMonotone {F | E ∩ F ∈ L} := by
  constructor
  · intro f hf hm
    change E ∩ (⋃ n, f n) ∈ L
    rw [Set.inter_iUnion]
    exact hL.increasing _ hf (fun n m hnm => inter_subset_inter_right E (hm hnm))
  · intro f hf hm
    change E ∩ (⋂ n, f n) ∈ L
    rw [Set.inter_iInter]
    exact hL.decreasing _ hf (fun n m hnm => inter_subset_inter_right E (hm hnm))

/-- The original two-intersection-classes proof, preceded by the complement class.
The sigma closure is obtained by finite unions followed by increasing unions. -/
theorem monotone_class_written {Ω : Type*} (A L : Set (Set Ω))
    (huniv : (univ : Set Ω) ∈ A)
    (hcompl : ∀ E ∈ A, Eᶜ ∈ A)
    (hinter : ∀ E ∈ A, ∀ F ∈ A, E ∩ F ∈ A)
    (hL : WrittenMonotone L) (hAL : A ⊆ L) :
    ∀ E, MeasurableSet[MeasurableSpace.generateFrom A] E → E ∈ L := by
  let H := monotoneHull A
  have hH : WrittenMonotone H := monotoneHull_closed A
  have hAH : A ⊆ H := fun E hE _ _ h => h hE
  have hHC : ∀ E ∈ H, Eᶜ ∈ H := by
    intro E hE
    exact hE _ (monotone_complement_class H hH) (fun F hF => hAH (hcompl F hF))
  have hfirst : ∀ E ∈ A, ∀ F ∈ H, E ∩ F ∈ H := by
    intro E hE F hF
    exact hF _ (monotone_intersection_class H hH E)
      (fun G hG => hAH (hinter E hE G hG))
  have hsecond : ∀ E ∈ H, ∀ F ∈ H, E ∩ F ∈ H := by
    intro E hE F hF
    exact hF _ (monotone_intersection_class H hH E) (by
      intro G hG
      change E ∩ G ∈ H
      simpa only [inter_comm] using hfirst G hG E hE)
  have hlam : Asakura.ManuscriptLambda H := by
    constructor
    · exact hAH huniv
    · intro E F hE hF _
      have h := hsecond F hF Eᶜ (hHC E hE)
      simpa only [sdiff_eq] using h
    · exact hH.increasing
  obtain ⟨m, hm⟩ := Asakura.manuscript_sigma_by_finite_unions H hlam hsecond
  have hgen : MeasurableSpace.generateFrom A ≤ m :=
    MeasurableSpace.generateFrom_le (fun E hE => (hm E).mpr (hAH hE))
  intro E hE
  exact ((hm E).mp (hgen E hE)) L hL hAL

end Asakura.FullAudit
