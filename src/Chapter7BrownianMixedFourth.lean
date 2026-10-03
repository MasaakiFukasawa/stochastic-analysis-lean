import Chapter7BrownianProjectionLaw
import Chapter7GaussianMixedFourth

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The mixed fourth moment of four actual linear transforms of one Brownian
increment. The covariance is computed from the diffusion matrix rows. -/
theorem brownian_transformed_mixed_fourth
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (B : BrownianSystem P d) (S : Fin 4 → Fin d → ℝ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    let X := fun i w => ∑ j,S i j*(B.W j (realTimeClamp t) w-B.W j (realTimeClamp s) w)
    let a := fun i k => (t-s)*(∑ j,S i j*S k j)
    Integrable (fun w => X 0 w*X 1 w*X 2 w*X 3 w) P ∧
    (∫ w,X 0 w*X 1 w*X 2 w*X 3 w ∂P)=a 0 1*a 2 3+a 0 2*a 1 3+a 0 3*a 1 2 := by
  classical
  dsimp only
  let X := fun i w => ∑ j,S i j*(B.W j (realTimeClamp t) w-B.W j (realTimeClamp s) w)
  let a := fun i k => (t-s)*(∑ j,S i j*S k j)
  let u := fun r q z j => S 0 j+r*S 1 j+q*S 2 j+z*S 3 j
  let v := fun r q z => (⟨(t-s)*(∑ j,(u r q z j)^2),
    mul_nonneg (sub_nonneg.mpr hst) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))⟩ : ℝ≥0)
  apply gaussian_mixed_fourth P X a v
  · intro r q z
    convert (brownian_projection_law P B s t hs hst (u r q z)).1 using 1
    funext w
    dsimp only [X,u]
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro r q z
    change (t-s)*(∑ j,(S 0 j+r*S 1 j+q*S 2 j+z*S 3 j)^2) = _
    dsimp only [a]
    have he j : (S 0 j+r*S 1 j+q*S 2 j+z*S 3 j)^2 =
      S 0 j*S 0 j+r^2*(S 1 j*S 1 j)+q^2*(S 2 j*S 2 j)+z^2*(S 3 j*S 3 j)+
      2*(r*(S 0 j*S 1 j)+q*(S 0 j*S 2 j)+z*(S 0 j*S 3 j)+
        r*q*(S 1 j*S 2 j)+r*z*(S 1 j*S 3 j)+q*z*(S 2 j*S 3 j)) := by ring
    simp only [he,mul_add,Finset.sum_add_distrib,← Finset.mul_sum]
    ring

end Asakura.Chapter7
