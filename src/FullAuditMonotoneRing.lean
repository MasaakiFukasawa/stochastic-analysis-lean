import FullAuditStieltjesSemiring

open MeasureTheory Set Filter
namespace Asakura.FullAudit

theorem monotone_difference_right_class {Ω : Type*} (L : Set (Set Ω))
    (hL : WrittenMonotone L) (E : Set Ω) : WrittenMonotone {F | E \ F ∈ L} := by
  constructor
  · intro f hf hm
    change E \ (⋃ n, f n) ∈ L
    rw [Set.sdiff_iUnion]
    exact hL.decreasing _ hf (fun n m hnm => sdiff_subset_sdiff_right (hm hnm))
  · intro f hf hm
    change E \ (⋂ n, f n) ∈ L
    rw [Set.sdiff_iInter]
    exact hL.increasing _ hf (fun n m hnm => sdiff_subset_sdiff_right (hm hnm))

theorem monotone_difference_left_class {Ω : Type*} (L : Set (Set Ω))
    (hL : WrittenMonotone L) (F : Set Ω) : WrittenMonotone {E | E \ F ∈ L} := by
  constructor
  · intro f hf hm
    change (⋃ n, f n) \ F ∈ L
    rw [Set.iUnion_sdiff]
    exact hL.increasing _ hf (fun n m hnm => sdiff_subset_sdiff_left (hm hnm))
  · intro f hf hm
    change (⋂ n, f n) \ F ∈ L
    have he : (⋂ n, f n) \ F = ⋂ n, f n \ F := by
      ext x
      simp only [Set.mem_sdiff,Set.mem_iInter]
      exact ⟨fun h n => ⟨h.1 n,h.2⟩,fun h => ⟨fun n => (h n).1,(h 0).2⟩⟩
    rw [he]
    exact hL.decreasing _ hf (fun n m hnm => sdiff_subset_sdiff_left (hm hnm))

/-- An exhausting set ring is enough for the same two-class proof. This allows
using bounded real intervals without pretending that one of them is all of R. -/
theorem monotone_class_exhausting_ring {Ω : Type*} (A L : Set (Set Ω))
    (hA : IsSetRing A) (E : ℕ → Set Ω) (hE : ∀ n, E n ∈ A)
    (hmono : Monotone E) (hcover : ⋃ n, E n = univ)
    (hL : WrittenMonotone L) (hAL : A ⊆ L) :
    ∀ F, MeasurableSet[MeasurableSpace.generateFrom A] F → F ∈ L := by
  let H := monotoneHull A
  have hH : WrittenMonotone H := monotoneHull_closed A
  have hAH : A ⊆ H := fun F hF _ _ h => h hF
  have hu : (univ : Set Ω) ∈ H := by rw [← hcover]; exact hH.increasing E (fun n => hAH (hE n)) hmono
  have hfirst : ∀ F ∈ A, ∀ G ∈ H, F \ G ∈ H := by
    intro F hF G hG
    exact hG _ (monotone_difference_right_class H hH F)
      (fun K hK => hAH (hA.sdiff_mem hF hK))
  have hsecond : ∀ F ∈ H, ∀ G ∈ H, F \ G ∈ H := by
    intro F hF G hG
    exact hF _ (monotone_difference_left_class H hH G) (fun K hK => hfirst K hK G hG)
  have hinter : ∀ F ∈ H, ∀ G ∈ H, F ∩ G ∈ H := by
    intro F hF G hG
    have h := hsecond F hF (F \ G) (hsecond F hF G hG)
    simpa only [sdiff_sdiff_right_self,inter_comm] using h
  have hlam : Asakura.ManuscriptLambda H := by
    constructor
    · exact hu
    · intro F G hF hG _; exact hsecond G hG F hF
    · exact hH.increasing
  obtain ⟨m,hm⟩ := Asakura.manuscript_sigma_by_finite_unions H hlam hinter
  have hgen : MeasurableSpace.generateFrom A ≤ m :=
    MeasurableSpace.generateFrom_le (fun F hF => (hm F).mpr (hAH hF))
  intro F hF
  exact ((hm F).mp (hgen F hF)) L hL hAL

/-- Extend the signed interval estimate to all Borel sets on R by the written
monotone-class argument and the exhaustion (-n,n]. -/
theorem signed_cs_real_intervals (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (ν : SignedMeasure ℝ)
    (hc : ∀ s t, s ≤ t → |ν (Ioc s t)| ≤ Real.sqrt (α.real (Ioc s t))*Real.sqrt (β.real (Ioc s t))) :
    ∀ F, MeasurableSet F → |ν F| ≤ Real.sqrt (α.real F)*Real.sqrt (β.real F) := by
  let C : Set (Set ℝ) := {F | ∃ s t, s ≤ t ∧ F = Ioc s t}
  have hC : IsSetSemiring C := IsSetSemiring.Ioc
  have hgen : borel ℝ = MeasurableSpace.generateFrom C := by
    rw [borel_eq_generateFrom_Ioc_le ℝ]
    congr 1
    ext F
    simp only [C,Set.mem_ofPred_eq]
    constructor <;> rintro ⟨s,t,hst,hF⟩ <;> exact ⟨s,t,hst,hF.symm⟩
  have hR := hC.isSetRing_supClosure
  have hgenR : borel ℝ = MeasurableSpace.generateFrom (supClosure C) := by
    rw [hgen]
    apply le_antisymm (MeasurableSpace.generateFrom_mono subset_supClosure)
    exact MeasurableSpace.generateFrom_le (fun F hF => measurableSet_generateFrom_of_mem_supClosure hF)
  have hh := monotone_class_exhausting_ring (supClosure C)
    {F | MeasurableSet F ∧ |ν F| ≤ Real.sqrt (α.real F)*Real.sqrt (β.real F)} hR
    (fun n => Ioc (-(n:ℝ)) n) (fun n => subset_supClosure ⟨-(n:ℝ),n,by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith,rfl⟩)
    (fun n m hnm => Ioc_subset_Ioc (neg_le_neg (by exact_mod_cast hnm)) (by exact_mod_cast hnm))
    (by
      ext x
      simp only [mem_iUnion,mem_Ioc,mem_univ,iff_true]
      obtain ⟨n,hn⟩ := exists_nat_gt |x|
      exact ⟨n,by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩)
    (signed_cs_monotone_class α β ν) (by
      intro F hF
      refine ⟨?_,signed_cs_supClosure α β ν C hC ?_ ?_ F hF⟩
      · change MeasurableSet[borel ℝ] F
        rw [hgenR]; exact MeasurableSpace.measurableSet_generateFrom hF
      · rintro F ⟨s,t,_,rfl⟩; exact measurableSet_Ioc
      · rintro F ⟨s,t,hst,rfl⟩; exact hc s t hst)
  intro F hF
  exact (hh F (by rwa [← hgenR])).2

end Asakura.FullAudit
