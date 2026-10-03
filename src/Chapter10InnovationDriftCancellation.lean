import Chapter10ConditionalDriftCancellation
import Chapter9ReverseTransitionFields

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The finite-variation terms of the innovation product formula have zero
conditional expectation, derived from the actual Gaussian error process. -/
theorem innovation_quadratic_drift_conditional_zero {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r n : ℕ} (B : BrownianSystem P n)
    (F : ℝ → Matrix (Fin d) (Fin d) ℝ) (L : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (hF : Continuous F) (hL : Continuous L)
    (E : Fin (d+r) → Fin n → ℝ → ℝ) (hE : ∀ i j,Continuous (E i j))
    (ξ : Ω → Fin (d+r) → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0)
    (T : ℝ) (hT : 0≤T) (N : Fin (d+r) → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin (d+r) → ℝ))
    (h : LinearStateWitness P B
      (fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))) E ξ T hT N X)
    (hind : ∀ t : Icc (0:ℝ) T,IndepFun (fun w i => X w t (headIndex i))
      (fun w (z : {u : Icc (0:ℝ) T // u.val≤t.val} × Fin r) => X w z.1.val (tailIndex z.2)) P)
    (s u : Icc (0:ℝ) T) (hsu : s.val≤u.val) (i j : Fin r) :
    P[(fun w => X w u (tailIndex j)*(∑ k,L u.val i k*X w u (headIndex k)))|
      nullAugmentedInformation (m := m) P (pathInformation T X tailIndex s)]=ᵐ[P]
      (fun _ => (0:ℝ)) := by
  letI : MeasurableSpace Ω := m
  let A := fun u => matrixOperatorMap (finiteBlocks (F u) 0 (L u) (0 : Matrix (Fin r) (Fin r) ℝ))
  apply conditional_linear_error_product_zero P _ _
    (null_augmented_mono P _ _ (path_information_mono T X tailIndex s u hsu))
    ((h.path_information_le P B A E ξ T hT N X tailIndex u).trans (B.le _))
    (fun k w => X w u (headIndex k)) (fun w => X w u (tailIndex j)) (fun k => L u.val i k)
  · intro k
    exact h.coordinate_memLp P B A E ξ T hT N X u (headIndex k)
  · exact h.coordinate_memLp P B A E ξ T hT N X u (tailIndex j)
  · exact (path_information_current T X tailIndex u j).mono (null_augmented_contains P _) le_rfl
  · intro k
    exact innovation_history_error_conditional_zero P B F L hF hL E hE ξ hξ hξg hξ0
      T hT N X h hind u u le_rfl k

end Asakura.Chapter10
