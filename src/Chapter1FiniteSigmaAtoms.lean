import FullAuditPartitionExercise
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory Set Function
open scoped BigOperators ENNReal
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def finiteSigmaAtoms {Ω : Type*} (G : MeasurableSpace Ω) := Set.range (@measurableAtom Ω G)

lemma finite_sigma_atom_measurable {Ω : Type*} (G : MeasurableSpace Ω)
    [Finite {s : Set Ω // MeasurableSet[G] s}] (x : Ω) : MeasurableSet[G] (@measurableAtom Ω G x) := by
  classical
  letI : MeasurableSpace Ω := G
  letI := Fintype.ofFinite {s : Set Ω // MeasurableSet[G] s}
  have he : measurableAtom x=⋂ s : {s : Set Ω // MeasurableSet s},if x∈s.val then s.val else univ := by
    ext y
    simp only [measurableAtom,mem_iInter]
    constructor
    · intro h s
      by_cases hx : x∈s.val
      · simpa [hx] using h s.val hx s.property
      · simp [hx]
    · intro h s hx hs
      simpa [hx] using h ⟨s,hs⟩
  rw [he]
  apply MeasurableSet.iInter
  intro s
  split_ifs <;> first | exact s.property | exact MeasurableSet.univ

instance finite_sigma_atoms_finite {Ω : Type*} (G : MeasurableSpace Ω)
    [Finite {s : Set Ω // MeasurableSet[G] s}] : Finite (finiteSigmaAtoms G) := by
  let f : finiteSigmaAtoms G → {s : Set Ω // MeasurableSet[G] s} := fun A =>
    ⟨A.val,by obtain ⟨x,hx⟩ := A.property; rw [← hx]; exact finite_sigma_atom_measurable G x⟩
  exact Finite.of_injective f (fun A B h => Subtype.ext (congrArg (fun s : {s : Set Ω // MeasurableSet[G] s} => s.val) h))

lemma finite_sigma_atoms_nonempty {Ω : Type*} (G : MeasurableSpace Ω) (A : finiteSigmaAtoms G) : A.val.Nonempty := by
  obtain ⟨x,hx⟩ := A.property
  exact ⟨x,hx ▸ @mem_measurableAtom_self Ω G x⟩

lemma finite_sigma_atoms_disjoint {Ω : Type*} (G : MeasurableSpace Ω) :
    Pairwise (Disjoint on (fun A : finiteSigmaAtoms G => A.val)) := by
  intro A B hAB
  obtain ⟨x,hx⟩ := A.property
  obtain ⟨y,hy⟩ := B.property
  change Disjoint A.val B.val
  rw [← hx,← hy]
  apply @disjoint_measurableAtom_of_notMem Ω G
  intro hm
  exact hAB (Subtype.ext (hx.symm.trans ((@measurableAtom_eq_of_mem Ω G x y hm).trans hy)))

lemma finite_sigma_set_as_union {Ω : Type*} (G : MeasurableSpace Ω)
    (s : Set Ω) (hs : MeasurableSet[G] s) :
    s=⋃ A : {A : finiteSigmaAtoms G // A.val⊆s},A.val.val := by
  ext x
  constructor
  · intro hx
    exact mem_iUnion.mpr ⟨⟨⟨@measurableAtom Ω G x,mem_range_self x⟩,
      @measurableAtom_subset Ω G s x hs hx⟩,@mem_measurableAtom_self Ω G x⟩
  · intro hx
    obtain ⟨A,hA⟩ := mem_iUnion.mp hx
    exact A.property hA

/-- Every event is a union of the nonempty atoms, and arbitrary atom unions
are distinct. This proves the 2^n event count used in the dimension exercise. -/
theorem finite_sigma_atoms_card {Ω : Type*} (G : MeasurableSpace Ω)
    [Finite {s : Set Ω // MeasurableSet[G] s}] :
    Nat.card {s : Set Ω // MeasurableSet[G] s}=2^Nat.card (finiteSigmaAtoms G) := by
  classical
  letI : MeasurableSpace Ω := G
  letI := Fintype.ofFinite {s : Set Ω // MeasurableSet[G] s}
  letI := Fintype.ofFinite (finiteSigmaAtoms G)
  let join : Set (finiteSigmaAtoms G) → {s : Set Ω // MeasurableSet s} := fun S =>
    ⟨⋃ A : S,A.val.val,MeasurableSet.iUnion (fun A => by
      obtain ⟨x,hx⟩ := A.val.property
      rw [← hx]; exact finite_sigma_atom_measurable G x)⟩
  have hinj : Injective join := by
    intro S R he
    have he' := congrArg (fun s : {s : Set Ω // MeasurableSet[G] s} => s.val) he
    apply Set.Subset.antisymm
    all_goals
      intro A hA
      obtain ⟨x,hx⟩ := finite_sigma_atoms_nonempty G A
    · have hh : x∈(join S).val := mem_iUnion.mpr ⟨⟨A,hA⟩,hx⟩
      rw [he'] at hh
      obtain ⟨B,hB⟩ := mem_iUnion.mp hh
      have hab : A=B.val := by
        by_contra hn
        exact Set.disjoint_left.mp (finite_sigma_atoms_disjoint G hn) hx hB
      exact hab ▸ B.property
    · have hh : x∈(join R).val := mem_iUnion.mpr ⟨⟨A,hA⟩,hx⟩
      rw [← he'] at hh
      obtain ⟨B,hB⟩ := mem_iUnion.mp hh
      have hab : A=B.val := by
        by_contra hn
        exact Set.disjoint_left.mp (finite_sigma_atoms_disjoint G hn) hx hB
      exact hab ▸ B.property
  have hsurj : Surjective join := by
    intro s
    exact ⟨{A | A.val⊆s.val},Subtype.ext (finite_sigma_set_as_union G s.val s.property).symm⟩
  have he := Nat.card_congr (Equiv.ofBijective join ⟨hinj,hsurj⟩)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_set] using he.symm

end Asakura.Chapter1Complete
