import EndToEndHJMFiniteMaturity

open MeasureTheory Set
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Extending a coefficient by zero in its maturity variable preserves both
joint and progressive measurability. A bound on the specified maturity set
becomes a bound on all maturities. -/
theorem finite_parameter_extension {Ω : Type} [MeasurableSpace Ω]
    (F : HalfClosedTime → MeasurableSpace Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (H : ℝ × (Ω × ℝ) → ℝ) (hm : Measurable H)
    (hp : ∀ b, 0 < b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod
        (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val)))) inferInstance
      (fun z : ℝ × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb : ∀ w b, 0 ≤ b → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ A, ∀ r ∈ Icc 0 b, |H (x,(w,r))| ≤ K) :
    let G := fun z : ℝ × (Ω × ℝ) => if z.1 ∈ A then H z else 0
    Measurable G ∧
    (∀ b, 0 < b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod
        (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val)))) inferInstance
      (fun z : ℝ × (Ω × Icc (0:ℝ) b) => G (z.1,(z.2.1,z.2.2.val)))) ∧
    (∀ w b, 0 ≤ b → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x r, r ∈ Icc 0 b → |G (x,(w,r))| ≤ K) ∧
    (∀ x ∈ A, ∀ w r, G (x,(w,r)) = H (x,(w,r))) := by
  dsimp only
  refine ⟨hm.ite (hA.preimage measurable_fst) measurable_const, ?_, ?_, ?_⟩
  · intro b hb
    exact (hp b hb).ite (hA.preimage measurable_fst) measurable_const
  · intro w b hzero
    obtain ⟨K,hK,hbound⟩ := hb w b hzero
    refine ⟨K,hK,?_⟩
    intro x r hr
    by_cases hx : x ∈ A
    · simpa only [if_pos hx] using hbound x hx r hr
    · simpa only [if_neg hx,abs_zero] using hK
  · intro x hx w r
    simp only [if_pos hx]

#print axioms finite_parameter_extension
end Asakura.EndToEnd
