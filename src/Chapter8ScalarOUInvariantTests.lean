import Chapter8ScalarOUActualLaw
import Chapter8OUStationaryTests
import Chapter8ScalarCoordinate
import Chapter4SDETransitionLipschitz

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem scalar_ou_lipschitz_square (θ σ : ℝ) :
    ∀ x y : Fin 1 → ℝ,(∑ i : Fin 1,(-θ*x 0- -θ*y 0)^2)+
      (∑ i : Fin 1,∑ j : Fin 1,(σ-σ)^2)≤θ^2*∑ i,(x i-y i)^2 := by
  intro x y
  simp only [Fin.sum_univ_one,sub_self,zero_pow (by decide : 2≠0),add_zero]
  nlinarith [sq_nonneg (θ*(x 0-y 0))]

/-- The actual scalar SDE has the Gaussian invariant tests used by the
long-time score theorem; no stationarity assumption on its initial point is made. -/
theorem scalar_ou_invariant_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (θ σ : ℝ) (hθ : 0<θ)
    (Z : (Fin 1 → ℝ) → HalfClosedTime → Ω → Fin 1 → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W (fun _ y => -θ*y 0) (fun _ _ _ => σ) (fun _ => x) (Z x))
    (t : ℝ) (ht : 0≤t) (f : (Fin 1 → ℝ) → ℝ) (hf : ContDiff ℝ (⊤:ℕ∞) f) (hs : HasCompactSupport f) :
    (∫ x,(∫ w,f (Z x (realTimeClamp t) w) ∂P) ∂(gaussianReal 0 (ouStationaryVariance θ σ hθ)).map scalarCoordinate.symm)=
      ∫ x,f x ∂(gaussianReal 0 (ouStationaryVariance θ σ hθ)).map scalarCoordinate.symm := by
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨Lf,hLf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hf (by simp)
  obtain ⟨K,hK⟩ := sde_transition_preserves_lipschitz P B (θ^2) (sq_nonneg _) _ _
    (scalar_ou_lipschitz_square θ σ) Z hZ t ht
  have hm := (hK f Lf hLf C hC).continuous.measurable
  rw [integral_map scalarCoordinate.symm.continuous.measurable.aemeasurable hm.aestronglyMeasurable,
    integral_map scalarCoordinate.symm.continuous.measurable.aemeasurable hf.continuous.aestronglyMeasurable]
  have he x : (∫ w,f (Z (scalarCoordinate.symm x) (realTimeClamp t) w) ∂P)=
      ∫ y,f (scalarCoordinate.symm y) ∂ouKernel θ σ hθ ⟨t,ht⟩ x := by
    have hl := scalar_ou_actual_law P B θ σ x hθ (Z (scalarCoordinate.symm x)) (hZ _) t ht
    have hh := hl.integral_comp (hf.continuous.comp scalarCoordinate.symm.continuous).aestronglyMeasurable
    simpa only [Function.comp_def,←scalarCoordinate_apply,scalarCoordinate.symm_apply_apply] using hh
  simp_rw [he]
  exact ou_stationary_tests θ σ hθ ⟨t,ht⟩ (fun y => f (scalarCoordinate.symm y))
    (hf.continuous.comp scalarCoordinate.symm.continuous) C (fun y => hC _)
end Asakura.Chapter8
