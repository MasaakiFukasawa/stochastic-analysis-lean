import PiLambda

/-! Original proof in app0.tex:42--104. No invocation of the pi-lambda theorem.
The finite unions and the two successive intersection classes are explicit. -/
open Set MeasureTheory
namespace Asakura

theorem manuscript_sigma_by_finite_unions {Ω : Type*} (L : Set (Set Ω))
    (hL : ManuscriptLambda L) (hinter : ∀ A ∈ L, ∀ B ∈ L, A ∩ B ∈ L) :
    ∃ m : MeasurableSpace Ω, ∀ A, MeasurableSet[m] A ↔ A ∈ L := by
  classical
  have hunion : ∀ A ∈ L, ∀ B ∈ L, A ∪ B ∈ L := by
    intro A hA B hB
    have heq : (Aᶜ ∩ Bᶜ)ᶜ = A ∪ B := by ext x; simp; tauto
    rw [← heq]
    exact hL.compl_mem (hinter Aᶜ (hL.compl_mem hA) Bᶜ (hL.compl_mem hB))
  have hcount : ∀ f : ℕ → Set Ω, (∀ n, f n ∈ L) → (⋃ n, f n) ∈ L := by
    intro f hf
    have hfin : ∀ s : Finset ℕ, (⋃ i ∈ s, f i) ∈ L := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hL.empty_mem
      | @insert a s ha ih =>
        rw [Finset.set_biUnion_insert]
        exact hunion _ (hf a) _ ih
    have h := hL.increasing_union (fun n => ⋃ i ∈ Finset.range n, f i)
      (fun n => hfin _) (by
        intro n m hnm x hx
        simp only [Set.mem_iUnion, Finset.mem_range] at hx ⊢
        obtain ⟨i, hi, hx⟩ := hx
        exact ⟨i, hi.trans_le hnm, hx⟩)
    have heq : (⋃ n, ⋃ i ∈ Finset.range n, f i) = ⋃ i, f i := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨n, i, hi, hx⟩; exact ⟨i, hx⟩
      · rintro ⟨i, hx⟩; exact ⟨i+1, i, Nat.lt_succ_self i, hx⟩
    rwa [heq] at h
  exact ⟨⟨(· ∈ L), hL.empty_mem, fun _ h => hL.compl_mem h, hcount⟩, fun _ => Iff.rfl⟩

def manuscriptLambdaHull {Ω : Type*} (P : Set (Set Ω)) : Set (Set Ω) :=
  {A | ∀ L : Set (Set Ω), ManuscriptLambda L → P ⊆ L → A ∈ L}

theorem manuscript_hull_lambda {Ω : Type*} (P : Set (Set Ω)) :
    ManuscriptLambda (manuscriptLambdaHull P) := by
  constructor
  · intro L hL hPL; exact hL.univ_mem
  · intro A B hA hB hAB L hL hPL
    exact hL.diff_mem (hA L hL hPL) (hB L hL hPL) hAB
  · intro A hA hmono L hL hPL
    exact hL.increasing_union A (fun n => hA n L hL hPL) hmono

theorem manuscript_intersection_class {Ω : Type*} (L : Set (Set Ω))
    (hL : ManuscriptLambda L) {A : Set Ω} (hA : A ∈ L) :
    ManuscriptLambda {B | A ∩ B ∈ L} := by
  constructor
  · simpa using hA
  · intro B C hB hC hBC
    have h := hL.diff_mem hB hC (Set.inter_subset_inter_right A hBC)
    have heq : A ∩ (C \ B) = (A ∩ C) \ (A ∩ B) := by ext x; simp; tauto
    change A ∩ (C \ B) ∈ L
    rwa [heq]
  · intro B hB hmono
    have h := hL.increasing_union (fun n => A ∩ B n) hB
      (fun n m hnm => Set.inter_subset_inter_right A (hmono hnm))
    change A ∩ (⋃ n, B n) ∈ L
    simpa only [Set.inter_iUnion] using h

theorem manuscript_pi_lambda_two_intersections {Ω : Type*}
    (P L : Set (Set Ω)) (hP : ∀ A ∈ P, ∀ B ∈ P, A ∩ B ∈ P)
    (hL : ManuscriptLambda L) (hPL : P ⊆ L) :
    ∀ A, MeasurableSet[MeasurableSpace.generateFrom P] A → A ∈ L := by
  let H := manuscriptLambdaHull P
  have hH : ManuscriptLambda H := manuscript_hull_lambda P
  have hPH : P ⊆ H := fun A hA _ _ hPL => hPL hA
  have hfirst : ∀ A ∈ P, ∀ B ∈ H, A ∩ B ∈ H := by
    intro A hA B hB
    exact hB _ (manuscript_intersection_class H hH (hPH hA))
      (fun C hC => hPH (hP A hA C hC))
  have hsecond : ∀ A ∈ H, ∀ B ∈ H, A ∩ B ∈ H := by
    intro A hA B hB
    exact hB _ (manuscript_intersection_class H hH hA) (by
      intro C hC
      simpa [Set.inter_comm] using hfirst C hC A hA)
  obtain ⟨m, hm⟩ := manuscript_sigma_by_finite_unions H hH hsecond
  have hgen : MeasurableSpace.generateFrom P ≤ m :=
    MeasurableSpace.generateFrom_le (fun A hA => (hm A).mpr (hPH hA))
  intro A hA
  exact ((hm A).mp (hgen A hA)) L hL hPL

end Asakura
