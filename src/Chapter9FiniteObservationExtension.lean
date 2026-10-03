import Chapter9ConditionalPiSystem
import Mathlib.MeasureTheory.Constructions.Cylinders

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Equality on every finite-observation rectangle extends to conditioning
on the full process, including uncountably many observation times. -/
theorem conditional_expectation_of_finite_observations {Ω ι E : Type*}
    [m : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → E) (hX : ∀ i,Measurable (X i))
    (Y Z : Ω → ℝ) (hY : Integrable Y P) (hZ : Integrable Z P)
    (hmZ : AEStronglyMeasurable[MeasurableSpace.comap (fun w i => X i w) MeasurableSpace.pi] Z P)
    (he : ∀ (I : Finset ι) (A : ι → Set E),(∀ i,MeasurableSet (A i)) →
      (∫ w in {w | ∀ i∈I,X i w∈A i},Y w ∂P)=
        (∫ w in {w | ∀ i∈I,X i w∈A i},Z w ∂P)) :
    P[Y|MeasurableSpace.comap (fun w i => X i w) MeasurableSpace.pi]=ᵐ[P] Z := by
  let C := {B : Set Ω | ∃ A∈squareCylinders (fun _ : ι => {A : Set E | MeasurableSet A}),
    (fun w i => X i w) ⁻¹' A=B}
  have hpi : IsPiSystem C :=
    IsPiSystem.comap (isPiSystem_squareCylinders (fun _ => (fun A hA B hB _ => hA.inter hB)) (by simp)) _
  have hgen : MeasurableSpace.comap (fun w i => X i w) MeasurableSpace.pi=MeasurableSpace.generateFrom C := by
    rw [←generateFrom_squareCylinders,MeasurableSpace.comap_generateFrom]
    rfl
  refine conditional_expectation_of_pi_system P _ (measurable_pi_iff.mpr hX).comap_le C hpi hgen ?_ Y Z hY hZ hmZ ?_
  · refine ⟨univ,⟨∅,fun _ => univ,by simp,by simp⟩,by simp⟩
  · rintro A ⟨B,⟨I,S,hS,rfl⟩,rfl⟩
    have hs : ∀ i,MeasurableSet (S i) := by simpa only [mem_univ_pi,mem_ofPred_eq] using hS
    have hset : (fun w i => X i w) ⁻¹' (I : Set ι).pi S={w | ∀ i∈I,X i w∈S i} := by
      ext w
      simp
    rw [hset]
    exact he I S hs
end Asakura.Chapter9
