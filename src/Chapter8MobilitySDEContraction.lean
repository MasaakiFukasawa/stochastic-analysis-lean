import Chapter8MobilityCoordinates
import Chapter8ActualSynchronousContraction

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- For a positive mobility matrix the actual synchronous SDE contraction
holds in the inverse-mobility norm, with rate kappa times its lower eigenvalue. -/
theorem mobility_sde_contraction {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (M : E ≃L[ℝ] E)
    (hs : M.toContinuousLinearMap.toLinearMap.IsSymmetric)
    (α κ : ℝ) (hα : 0<α) (hκ : 0<κ) (hM : ∀ z,α*‖z‖^2≤⟪z,M z⟫)
    (g : E → E) (hg : Continuous g)
    (hmono : ∀ x y,κ*‖x-y‖^2≤⟪x-y,g x-g y⟫)
    (σ : Fin d → Fin n → ℝ) :
    ∃ A : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      (∀ z,‖A z‖^2=⟪z,M.symm z⟫) ∧
      ∀ (ξ ζ : Ω → Fin d → ℝ) (X Y : HalfClosedTime → Ω → Fin d → ℝ),
        VectorSDESolution P B.F B.W (fun i x => -(e.symm (M (g (e x))) i)) (fun i j _ => σ i j) ξ X →
        VectorSDESolution P B.F B.W (fun i x => -(e.symm (M (g (e x))) i)) (fun i j _ => σ i j) ζ Y →
        ∀ᵐ w ∂P,∀ t≥0,‖A (e (X (realTimeClamp t) w))-A (e (Y (realTimeClamp t) w))‖≤
          Real.exp (-(κ*α)*t)*‖A (e (ξ w))-A (e (ζ w))‖ := by
  obtain ⟨A,hAi,hAn,hAb⟩ := mobility_coordinates M hs α hα hM
  refine ⟨A,hAn,?_⟩
  intro ξ ζ X Y hX hY
  let f := fun x => e.symm (M (g (e x)))
  have hf : Continuous f := by fun_prop
  have hAm x y : (κ*α)*‖(e.trans A) x-(e.trans A) y‖^2≤
      ⟪(e.trans A) x-(e.trans A) y,(e.trans A) (f x)-(e.trans A) (f y)⟫ := by
    have hn := mul_le_mul_of_nonneg_left (hAb (e x-e y)) hκ.le
    have hm := hmono (e x) (e y)
    have hi := hAi (e x-e y) (g (e x)-g (e y))
    simp only [ContinuousLinearEquiv.trans_apply,f,e.apply_symm_apply]
    rw [←map_sub A,←map_sub A,←map_sub M,hi]
    nlinarith
  exact actual_synchronous_contraction P B (e.trans A) f hf σ (κ*α) hAm ξ ζ X Y hX hY

end Asakura.Chapter8
