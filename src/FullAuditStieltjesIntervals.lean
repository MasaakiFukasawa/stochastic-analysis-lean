import FullAuditStieltjesSemiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set
namespace Asakura.FullAudit

/-- Pull back a semiring, preserving the finite disjoint decomposition of differences. -/
theorem semiring_preimage {Ω S : Type*} (f : Ω → S) (C : Set (Set S))
    (hC : IsSetSemiring C) : IsSetSemiring (Set.preimage f '' C) := by
  classical
  constructor
  · exact ⟨∅, hC.empty_mem, rfl⟩
  · rintro _ ⟨s,hs,rfl⟩ _ ⟨t,ht,rfl⟩
    exact ⟨s∩t,hC.inter_mem s hs t ht,rfl⟩
  · rintro _ ⟨s,hs,rfl⟩ _ ⟨t,ht,rfl⟩
    obtain ⟨I,hI,hd,he⟩ := hC.sdiff_eq_sUnion' s hs t ht
    refine ⟨I.image (Set.preimage f), ?_, ?_, ?_⟩
    · intro E hE
      obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hE
      exact ⟨F,hI hF,rfl⟩
    · intro E hE F hF hEF
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hE
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hF
      exact Disjoint.preimage f (hd hs ht (fun h => hEF (congrArg (Set.preimage f) h)))
    · rw [← Set.preimage_sdiff, he]
      ext x
      simp

/-- Half-open intervals on the actual bounded domain of the Stieltjes measures. -/
def boundedIntervalFamily (a b : ℝ) : Set (Set (Ioc a b)) :=
  Set.preimage (fun x : Ioc a b => (x:ℝ)) ''
    {E : Set ℝ | ∃ l u, l ≤ u ∧ E=Ioc l u}

theorem boundedIntervalFamily_semiring (a b : ℝ) :
    IsSetSemiring (boundedIntervalFamily a b) :=
  semiring_preimage _ _ IsSetSemiring.Ioc

theorem boundedIntervalFamily_univ (a b : ℝ) (hab : a ≤ b) :
    (univ : Set (Ioc a b)) ∈ boundedIntervalFamily a b := by
  refine ⟨Ioc a b,⟨a,b,hab,rfl⟩,?_⟩
  ext x
  simp [x.property]

theorem boundedIntervalFamily_generates (a b : ℝ) :
    (inferInstance : MeasurableSpace (Ioc a b)) =
      MeasurableSpace.generateFrom (boundedIntervalFamily a b) := by
  change MeasurableSpace.comap (fun x : Ioc a b => (x:ℝ)) (borel ℝ) = _
  rw [borel_eq_generateFrom_Ioc_le ℝ, MeasurableSpace.comap_generateFrom]
  congr 1
  ext E
  simp only [boundedIntervalFamily, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨F,⟨l,u,hlu,hF⟩,hE⟩
    exact ⟨F,⟨l,u,hlu,hF.symm⟩,hE⟩
  · rintro ⟨F,⟨l,u,hlu,hF⟩,hE⟩
    exact ⟨F,⟨l,u,hlu,hF.symm⟩,hE⟩

/-- The measure-theoretic content of the manuscript's Stieltjes theorem:
interval mass estimates imply the full variation-integral estimate. -/
theorem stieltjes_integral_from_intervals (a b : ℝ) (hab : a ≤ b)
    (α β : Measure (Ioc a b)) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (ν : SignedMeasure (Ioc a b))
    (hc : ∀ l u : ℝ, l ≤ u →
      |ν {x | l < (x:ℝ) ∧ (x:ℝ) ≤ u}| ≤
        Real.sqrt (α.real {x | l < (x:ℝ) ∧ (x:ℝ) ≤ u})*
        Real.sqrt (β.real {x | l < (x:ℝ) ∧ (x:ℝ) ≤ u}))
    (f g : Ioc a b → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal |f x*g x| ∂ν.totalVariation) ≤
      (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂α)^(1/2:ℝ)*
      (∫⁻ x, ENNReal.ofReal ((g x)^2) ∂β)^(1/2:ℝ) := by
  apply stieltjes_integral_from_semiring α β ν (boundedIntervalFamily a b)
    (boundedIntervalFamily_semiring a b) (boundedIntervalFamily_generates a b)
    (boundedIntervalFamily_univ a b hab) ?_ f g hf hg
  rintro E ⟨F,⟨l,u,hlu,rfl⟩,rfl⟩
  exact hc l u hlu

/-- Restrict the mass hypotheses to the endpoint range stated in the manuscript. -/
theorem stieltjes_integral_bounded_intervals (a b : ℝ) (hab : a ≤ b)
    (α β : Measure (Ioc a b)) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (ν : SignedMeasure (Ioc a b))
    (hc : ∀ s t : ℝ, a ≤ s → s < t → t ≤ b →
      |ν {x | s < (x:ℝ) ∧ (x:ℝ) ≤ t}| ≤
        Real.sqrt (α.real {x | s < (x:ℝ) ∧ (x:ℝ) ≤ t})*
        Real.sqrt (β.real {x | s < (x:ℝ) ∧ (x:ℝ) ≤ t}))
    (f g : Ioc a b → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal |f x*g x| ∂ν.totalVariation) ≤
      (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂α)^(1/2:ℝ)*
      (∫⁻ x, ENNReal.ofReal ((g x)^2) ∂β)^(1/2:ℝ) := by
  apply stieltjes_integral_from_intervals a b hab α β ν ?_ f g hf hg
  intro l u hlu
  have he : {x : Ioc a b | l < (x:ℝ) ∧ (x:ℝ) ≤ u} =
      {x : Ioc a b | max a l < (x:ℝ) ∧ (x:ℝ) ≤ min b u} := by
    ext x
    simp only [mem_setOf_eq,max_lt_iff,le_min_iff]
    exact ⟨fun h => ⟨⟨x.property.1,h.1⟩,x.property.2,h.2⟩,
      fun h => ⟨h.1.2,h.2.2⟩⟩
  rw [he]
  by_cases hst : max a l < min b u
  · exact hc _ _ (le_max_left _ _) hst (min_le_left _ _)
  · have hem : {x : Ioc a b | max a l < (x:ℝ) ∧ (x:ℝ) ≤ min b u} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hst (hx.1.trans_le hx.2)
    rw [hem]
    simp [Measure.real_def]

end Asakura.FullAudit
