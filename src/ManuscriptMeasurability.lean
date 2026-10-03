import ManuscriptPiLambda
import MeasurabilityCriteria
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
namespace Asakura

/-- app0:117: the sigma algebra of sets with measurable inverse image. -/
theorem manuscript_measurable_generators {Ω S : Type*} [m : MeasurableSpace Ω]
    (P : Set (Set S)) (f : Ω → S) (hP : ∀ A ∈ P, MeasurableSet (f ⁻¹' A)) :
    @Measurable Ω S m (MeasurableSpace.generateFrom P) f := by
  let G : MeasurableSpace S := {
    MeasurableSet' := fun A => MeasurableSet (f ⁻¹' A)
    measurableSet_empty := by simp
    measurableSet_compl := by intro A hA; simpa using hA.compl
    measurableSet_iUnion := by intro A hA; simpa using MeasurableSet.iUnion hA }
  have h : MeasurableSpace.generateFrom P ≤ G := MeasurableSpace.generateFrom_le hP
  exact fun A hA => h A hA

/-- app0:133: open inverse images and the previous generator argument. -/
theorem manuscript_continuous_measurable {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] (f : S → T) (hf : Continuous f) :
    @Measurable S T (borel S) (borel T) f := by
  letI := borel S
  apply manuscript_measurable_generators
  intro A hA
  exact MeasurableSpace.measurableSet_generateFrom (hf.isOpen_preimage A hA)

/-- Countable subunions of basis opens, the explicit step used twice in app0. -/
theorem manuscript_open_from_basis {S : Type*} [TopologicalSpace S]
    [SecondCountableTopology S] (m : MeasurableSpace S) (B : Set (Set S))
    (hB : IsTopologicalBasis B) (hm : ∀ A ∈ B, MeasurableSet[m] A)
    {U : Set S} (hU : IsOpen U) : MeasurableSet[m] U := by
  obtain ⟨C, hCB, hUC⟩ := hB.open_eq_sUnion hU
  obtain ⟨D, hDcount, hDC, hDCunion⟩ := isOpen_sUnion_countable C
    (fun A hA => hB.isOpen (hCB hA))
  rw [hUC, ← hDCunion]
  exact MeasurableSet.sUnion hDcount (fun A hA => hm A (hCB (hDC hA)))

/-- app0:142: countable unions of balls, followed by inverse-image closure. -/
theorem manuscript_measurable_balls {Ω S : Type*} [MeasurableSpace Ω]
    [MetricSpace S] [SeparableSpace S] (f : Ω → S)
    (hf : ∀ a r, 0 < r → MeasurableSet (f ⁻¹' Metric.ball a r)) :
    @Measurable Ω S _ (borel S) f := by
  let B : Set (Set S) := {U | ∃ a r, 0 < r ∧ U = Metric.ball a r}
  have hB : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro U ⟨a, r, hr, rfl⟩; exact Metric.isOpen_ball
    · intro x U hx hU
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
      exact ⟨Metric.ball x r, ⟨x,r,hr,rfl⟩, Metric.mem_ball_self hr, hsub⟩
  let G := MeasurableSpace.map f (inferInstance : MeasurableSpace Ω)
  apply manuscript_measurable_generators
  intro U hU
  apply manuscript_open_from_basis G B hB _ hU
  rintro A ⟨a,r,hr,rfl⟩
  exact hf a r hr

/-- app0:158, first inclusion: countably many open rectangles. -/
theorem manuscript_borel_le_rectangles {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] [SecondCountableTopology S] [SecondCountableTopology T] :
    borel (S × T) ≤ MeasurableSpace.generateFrom
      (Set.image2 (· ×ˢ ·) {A | MeasurableSet[borel S] A} {B | MeasurableSet[borel T] B}) := by
  apply MeasurableSpace.generateFrom_le
  intro U hU
  apply manuscript_open_from_basis _ _ (isTopologicalBasis_opens.prod isTopologicalBasis_opens) _ hU
  rintro A ⟨V, hV, W, hW, rfl⟩
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨V, MeasurableSpace.measurableSet_generateFrom hV,
    W, MeasurableSpace.measurableSet_generateFrom hW, rfl⟩

/-- Fixed-left-set sigma class F_A, including its relative-complement step. -/
@[instance_reducible] def manuscriptRightRectangleClass {S T : Type*} (m : MeasurableSpace (S × T))
    (A : Set S) (hA : MeasurableSet[m] (A ×ˢ (Set.univ : Set T))) : MeasurableSpace T where
  MeasurableSet' B := MeasurableSet[m] (A ×ˢ B)
  measurableSet_empty := by simp
  measurableSet_compl := by
    intro B hB
    have heq : A ×ˢ Bᶜ = (A ×ˢ (Set.univ : Set T)) \ (A ×ˢ B) := by ext x; simp; tauto
    rw [heq]
    exact hA.diff hB
  measurableSet_iUnion := by
    intro B hB
    simpa only [Set.prod_iUnion] using MeasurableSet.iUnion hB

/-- Fixed-right-set sigma class F_B, the second stage. -/
@[instance_reducible] def manuscriptLeftRectangleClass {S T : Type*} (m : MeasurableSpace (S × T))
    (B : Set T) (hB : MeasurableSet[m] ((Set.univ : Set S) ×ˢ B)) : MeasurableSpace S where
  MeasurableSet' A := MeasurableSet[m] (A ×ˢ B)
  measurableSet_empty := by simp
  measurableSet_compl := by
    intro A hA
    have heq : Aᶜ ×ˢ B = ((Set.univ : Set S) ×ˢ B) \ (A ×ˢ B) := by ext x; simp; tauto
    rw [heq]
    exact hB.diff hA
  measurableSet_iUnion := by
    intro A hA
    have heq : (⋃ i, A i) ×ˢ B = ⋃ i, A i ×ˢ B := by ext x; simp
    rw [heq]
    exact MeasurableSet.iUnion hA

/-- app0:158, reverse inclusion: the manuscript's two sigma classes. -/
theorem manuscript_rectangles_le_borel {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] :
    MeasurableSpace.generateFrom
      (Set.image2 (· ×ˢ ·) {A | MeasurableSet[borel S] A} {B | MeasurableSet[borel T] B})
      ≤ borel (S × T) := by
  have hfirst : ∀ A : Set S, IsOpen A → ∀ B : Set T, MeasurableSet[borel T] B →
      MeasurableSet[borel (S × T)] (A ×ˢ B) := by
    intro A hA
    let G := manuscriptRightRectangleClass (borel (S × T)) A
      (MeasurableSpace.measurableSet_generateFrom (hA.prod isOpen_univ))
    have hG : borel T ≤ G := MeasurableSpace.generateFrom_le (fun B hB =>
      MeasurableSpace.measurableSet_generateFrom (hA.prod hB))
    exact fun B hB => hG B hB
  apply MeasurableSpace.generateFrom_le
  rintro C ⟨A,hA,B,hB,rfl⟩
  let G := manuscriptLeftRectangleClass (borel (S × T)) B (hfirst _ isOpen_univ B hB)
  have hG : borel S ≤ G := MeasurableSpace.generateFrom_le
    (fun U hU => hfirst U hU B hB)
  exact hG A hA

theorem manuscript_product_borel {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] [SecondCountableTopology S] [SecondCountableTopology T] :
    borel (S × T) = MeasurableSpace.generateFrom
      (Set.image2 (· ×ˢ ·) {A | MeasurableSet[borel S] A} {B | MeasurableSet[borel T] B}) :=
  le_antisymm manuscript_borel_le_rectangles manuscript_rectangles_le_borel

/-- app0:184: inverse images of rectangles are intersections. -/
theorem manuscript_measurable_pair {Ω S T : Type*} [MeasurableSpace Ω]
    [TopologicalSpace S] [TopologicalSpace T] [SecondCountableTopology S]
    [SecondCountableTopology T] (f : Ω → S) (g : Ω → T)
    (hf : @Measurable Ω S _ (borel S) f) (hg : @Measurable Ω T _ (borel T) g) :
    @Measurable Ω (S × T) _ (borel (S × T)) (fun x => (f x, g x)) := by
  rw [manuscript_product_borel]
  apply manuscript_measurable_generators
  rintro U ⟨A,hA,B,hB,rfl⟩
  exact (hf hA).inter (hg hB)

/-- app0:238: inverse image of a ray under a supremum is a countable union. -/
theorem manuscript_measurable_sup {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → EReal) (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => ⨆ n, f n x) := by
  apply measurable_ereal_from_real_rays
  intro a
  have heq : {x | (a : EReal) < ⨆ n, f n x} = ⋃ n, {x | (a : EReal) < f n x} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_iUnion, lt_iSup_iff]
  rw [heq]
  exact MeasurableSet.iUnion (fun n => measurableSet_lt measurable_const (hf n))

/-- app0:253: monotone inverse images of intervals are intervals, hence Borel. -/
theorem manuscript_monotone_measurable (f : ℝ≥0∞ → ℝ≥0∞) (hf : Monotone f) :
    Measurable f := by
  apply measurable_of_Ioi
  intro a
  exact (ordConnected_Ioi.preimage_mono hf).measurableSet

/-- app0:238: infima follow from suprema by continuous sign reversal. -/
theorem manuscript_measurable_inf {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → EReal) (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => ⨅ n, f n x) := by
  have h := (manuscript_measurable_sup (fun n x => -f n x) (fun n => (hf n).neg)).neg
  have heq : ∀ x, -(⨆ n, -f n x) = ⨅ n, f n x := by
    intro x
    have he := EReal.negOrderIso.map_iSup (fun n => -f n x)
    change -(⨆ n, -f n x) = ⨅ n, -(-f n x) at he
    simpa only [neg_neg] using he
  change Measurable (fun x => -(⨆ n, -f n x)) at h
  simpa only [heq] using h

/-- app0:200--212: pair the measurable maps and compose with continuous operations. -/
theorem manuscript_measurable_vector_sum_dot {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (f g : Ω → Fin d → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x+g x) ∧
      Measurable (fun x => ∑ i : Fin d, f x i*g x i) := by
  have hpair := hf.prodMk hg
  have hadd : Continuous (fun z : (Fin d → ℝ) × (Fin d → ℝ) => z.1+z.2) :=
    continuous_fst.add continuous_snd
  have hdot : Continuous (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ∑ i : Fin d, z.1 i*z.2 i) := by
    fun_prop
  exact ⟨hadd.measurable.comp hpair,hdot.measurable.comp hpair⟩

end Asakura
