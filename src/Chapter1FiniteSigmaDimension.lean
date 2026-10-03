import Chapter1FiniteSigmaAtoms
import Chapter1FiniteCellDimension

open MeasureTheory Set Function
open scoped BigOperators ENNReal
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

lemma finite_sigma_atoms_generate {Ω : Type*} (G : MeasurableSpace Ω)
    [Finite {s : Set Ω // MeasurableSet[G] s}] :
    MeasurableSpace.generateFrom (range (fun A : finiteSigmaAtoms G => A.val))=G := by
  letI := Fintype.ofFinite (finiteSigmaAtoms G)
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨A,rfl⟩
    obtain ⟨x,hx⟩ := A.property
    dsimp only
    rw [← hx]
    exact finite_sigma_atom_measurable G x
  · intro s hs
    rw [finite_sigma_set_as_union G s hs]
    apply MeasurableSet.iUnion
    intro A
    exact MeasurableSpace.measurableSet_generateFrom (mem_range_self A.val)

lemma finite_sigma_atoms_cover {Ω : Type*} (G : MeasurableSpace Ω) :
    (⋃ A : finiteSigmaAtoms G,A.val)=univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨⟨@measurableAtom Ω G x,mem_range_self x⟩,@mem_measurableAtom_self Ω G x⟩

/-- If a finite sigma algebra has 2^n events and no nonempty null event,
its L² space has dimension n. All atom and quotient-space arguments are derived. -/
theorem finite_sigma_L2_dimension {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    [Finite {s : Set Ω // MeasurableSet[G] s}]
    (n : ℕ) (hcard : Nat.card {s : Set Ω // MeasurableSet[G] s}=2^n)
    (hpos : ∀ s,MeasurableSet[G] s → s.Nonempty → 0<P s) :
    letI : MeasurableSpace Ω := m
    Module.finrank ℝ (lpMeas ℝ ℝ G 2 P)=n := by
  classical
  letI : MeasurableSpace Ω := m
  letI := Fintype.ofFinite (finiteSigmaAtoms G)
  let A := fun a : finiteSigmaAtoms G => a.val
  have hAG a : MeasurableSet[G] (A a) := by
    obtain ⟨x,hx⟩ := a.property
    rw [show A a=@measurableAtom Ω G x from hx.symm]
    exact finite_sigma_atom_measurable G x
  have hA a : MeasurableSet (A a) := hG _ (hAG a)
  have hd : Pairwise (Disjoint on A) := finite_sigma_atoms_disjoint G
  have hcover : ∑ a,P (A a)=1 := by
    have he := measure_iUnion hd hA (μ := P)
    rw [finite_sigma_atoms_cover G,measure_univ] at he
    simpa only [tsum_fintype] using he.symm
  have hdim := finite_cell_L2_dimension P A hA hd hcover
    (fun a => hpos _ (hAG a) (finite_sigma_atoms_nonempty G a))
  have hgen : (⨆ a,MeasurableSpace.comap ((A a).indicator (fun _ => (1:ℝ))) inferInstance)=G :=
    (Asakura.FullAudit.indicator_generated_sigma A).trans (finite_sigma_atoms_generate G)
  rw [hgen] at hdim
  have hc : Nat.card (finiteSigmaAtoms G)=n :=
    Nat.pow_right_injective (by norm_num : 2≤2) ((finite_sigma_atoms_card G).symm.trans hcard)
  simpa only [Nat.card_eq_fintype_card] using hdim.trans (by simpa only [Nat.card_eq_fintype_card] using hc)

end Asakura.Chapter1Complete
