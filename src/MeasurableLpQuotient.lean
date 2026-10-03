import Appendix

open MeasureTheory
open scoped ENNReal
namespace Asakura
variable {Ω B : Type*} [MeasurableSpace Ω] [NormedAddCommGroup B]
  [MeasurableSpace B] [BorelSpace B] {p : ℝ≥0∞} {μ : Measure Ω}

abbrev MeasurableLp (B : Type*) [NormedAddCommGroup B] [MeasurableSpace B]
    (p : ℝ≥0∞) (μ : Measure Ω) := {f : Ω → B // Measurable f ∧ MemLp f p μ}

instance measurableLpSetoid : Setoid (MeasurableLp B p μ) where
  r f g := f.val =ᵐ[μ] g.val
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl,fun h => h.symm,fun h₁ h₂ => h₁.trans h₂⟩

noncomputable def measurableLpQuotientMap : Quotient (measurableLpSetoid (B := B) (p := p) (μ := μ)) → Lp B p μ :=
  Quotient.lift (fun f => f.property.2.toLp f.val)
    (fun f g h => (f.property.2.toLp_eq_toLp_iff g.property.2).mpr h)

lemma measurableLpQuotientMap_bijective : Function.Bijective
    (measurableLpQuotientMap (B := B) (p := p) (μ := μ)) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | h f =>
      induction b using Quotient.inductionOn with | h g =>
        intro he
        apply Quotient.sound
        exact (f.property.2.toLp_eq_toLp_iff g.property.2).mp he
  · intro f
    refine ⟨Quotient.mk _ ⟨f,(Lp.stronglyMeasurable f).measurable,Lp.memLp f⟩,?_⟩
    exact Lp.toLp_coeFn f (Lp.memLp f)

noncomputable def measurableLpQuotientEquiv :
    Quotient (measurableLpSetoid (B := B) (p := p) (μ := μ)) ≃ Lp B p μ :=
  Equiv.ofBijective measurableLpQuotientMap measurableLpQuotientMap_bijective

/-- The quotient correspondence preserves exactly the manuscript's Lp distance. -/
lemma measurableLpQuotient_distance (f g : MeasurableLp B p μ) :
    edist (measurableLpQuotientEquiv (Quotient.mk _ f))
      (measurableLpQuotientEquiv (Quotient.mk _ g)) = eLpNorm (f.val-g.val) p μ :=
  Lp.edist_toLp_toLp f.val g.val f.property.2 g.property.2
end Asakura
