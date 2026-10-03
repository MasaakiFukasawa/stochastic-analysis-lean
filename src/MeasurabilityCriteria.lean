import Extended
import Mathlib.MeasureTheory.MeasurableSpace.Prod
open MeasureTheory Set TopologicalSpace
namespace Asakura

/-- A.2: positive-radius balls suffice for a separable metric target. -/
theorem measurable_from_balls {Ω S : Type*} [MeasurableSpace Ω]
    [MetricSpace S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (f : Ω → S) (h : ∀ a r, 0 < r → MeasurableSet (f ⁻¹' Metric.ball a r)) :
    Measurable f := by
  let P : Set (Set S) := {U | ∃ a r, 0 < r ∧ U = Metric.ball a r}
  have hb : IsTopologicalBasis P := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro U ⟨a, r, hr, rfl⟩
      exact Metric.isOpen_ball
    · intro a U ha hU
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU a ha
      exact ⟨Metric.ball a r, ⟨a, r, hr, rfl⟩, Metric.mem_ball_self hr, hsub⟩
  have hm : @Measurable Ω S _ (MeasurableSpace.generateFrom P) f := by
    apply measurable_generateFrom
    rintro U ⟨a, r, hr, rfl⟩
    exact h a r hr
  have hms : (inferInstance : MeasurableSpace S) = MeasurableSpace.generateFrom P :=
    (BorelSpace.measurable_eq (α := S)).trans hb.borel_eq_generateFrom
  intro U hU
  exact hm ((congrArg (fun m : MeasurableSpace S => m.MeasurableSet' U) hms).mp hU)

/-- A.2: identify the product Borel space with the sigma algebra of rectangles. -/
theorem product_borel_rectangles {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [SecondCountableTopology S] [SecondCountableTopology T]
    [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T] :
    borel (S × T) = MeasurableSpace.generateFrom
      (Set.image2 (· ×ˢ ·) {A : Set S | MeasurableSet A} {B : Set T | MeasurableSet B}) := by
  rw [generateFrom_prod]
  exact (product_borel (S := S) (T := T)).symm

/-- A.2: finite real thresholds suffice even for signed extended-real functions. -/
theorem measurable_ereal_from_real_rays {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → EReal) (h : ∀ a : ℝ, MeasurableSet {x | (a : EReal) < f x}) :
    Measurable f := by
  apply measurable_of_Ioi
  intro a
  induction a using EReal.rec with
  | top => simpa using (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  | coe a => exact h a
  | bot =>
    have heq : f ⁻¹' Ioi ⊥ = ⋃ n : ℤ, {x | ((n : ℝ) : EReal) < f x} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := EReal.exists_between_coe_real hx
        obtain ⟨n, hn⟩ := exists_int_lt y
        exact ⟨n, (EReal.coe_lt_coe_iff.mpr hn).trans hyx⟩
      · rintro ⟨n, hn⟩
        exact bot_lt_of_lt hn
    rw [heq]
    exact MeasurableSet.iUnion (fun n => h n)

/-- B.1: Minkowski for arbitrary measurable representatives, including infinite norms. -/
theorem minkowski_extended {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (p : ENNReal) (hp : 1 ≤ p) (f g : Ω → E) :
    eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := eLpNorm_add_le hp
/-- A.2: the vector-valued sum and the Euclidean dot product. -/
theorem measurable_vector_sum_dot {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (f g : Ω → Fin d → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x + g x) ∧
      Measurable (fun x => ∑ i : Fin d, f x i * g x i) := by
  refine ⟨hf.add hg, ?_⟩
  exact Finset.measurable_sum _ (fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hg))

end Asakura
