import EndToEndCoefficientNullRepair

open MeasureTheory Set Filter
open scoped Classical
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Finite-maturity coefficient bounds need hold only almost surely and
 only on the maturity set. Zero extension and a common null repair provide
 exactly the representatives needed by the constructed parameter integrals. -/
theorem finite_coefficient_repair {Ω : Type} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (A : Set ℝ) (hA : MeasurableSet A)
    (H : ℝ × (Ω × ℝ) → ℝ) (hm : Measurable H)
    (hp : ∀ b,0 < b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod
        (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : ℝ × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb : ∀ᵐ w ∂P, ∀ b,0 ≤ b → ∃ K : ℝ,0 ≤ K ∧
      ∀ x ∈ A, ∀ r ∈ Icc 0 b, |H (x,(w,r))| ≤ K) :
    ∃ G : ℝ × (Ω × ℝ) → ℝ, Measurable G ∧
    (∀ b,0 < b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod
        (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : ℝ × (Ω × Icc (0:ℝ) b) => G (z.1,(z.2.1,z.2.2.val)))) ∧
    (∀ w b,0 ≤ b → ∃ K : ℝ,0 ≤ K ∧
      ∀ x r,r ∈ Icc 0 b → |G (x,(w,r))| ≤ K) ∧
    (∀ᵐ w ∂P,∀ x ∈ A,∀ r,G (x,(w,r))=H (x,(w,r))) := by
  let G0 := fun z : ℝ × (Ω × ℝ) => if z.1 ∈ A then H z else 0
  have hm0 : Measurable G0 := hm.ite (hA.preimage measurable_fst) measurable_const
  have hp0 b (hb : 0 < b) : @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod
        (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : ℝ × (Ω × Icc (0:ℝ) b) => G0 (z.1,(z.2.1,z.2.2.val))) :=
    (hp b hb).ite (hA.preimage measurable_fst) measurable_const
  have hb0 : ∀ᵐ w ∂P,∀ b,0 ≤ b → ∃ K : ℝ,0 ≤ K ∧
      ∀ x r,r ∈ Icc 0 b → |G0 (x,(w,r))| ≤ K := by
    filter_upwards [hb] with w hw
    intro b hb
    obtain ⟨K,hK,hbound⟩ := hw b hb
    refine ⟨K,hK,?_⟩
    intro x r hr
    by_cases hx : x ∈ A
    · simpa only [G0,if_pos hx] using hbound x hx r hr
    · simpa only [G0,if_neg hx,abs_zero] using hK
  obtain ⟨G,hGm,hGp,hGb,he⟩ := parameter_coefficient_null_repair P B G0 hm0 hp0 hb0
  refine ⟨G,hGm,hGp,hGb,?_⟩
  filter_upwards [he] with w hw
  intro x hx r
  simpa only [G0,if_pos hx] using hw x r

#print axioms finite_coefficient_repair
end Asakura.EndToEnd
