import Chapter10InnovationIntegratedDrift
import Chapter10ActualProductIncrements
import Chapter10StoppedConditionalIncrement
import Chapter10ConditionalProductAssembly
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
theorem innovation_product_conditional_increment {Ω : Type*} [m : MeasurableSpace Ω]
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
    (s t : Icc (0:ℝ) T) (hst : s.val≤t.val) (i j : Fin r) :
    P[(fun w => X w t (tailIndex i)*X w t (tailIndex j)-
      X w s (tailIndex i)*X w s (tailIndex j))|
      nullAugmentedInformation (m := m) P (pathInformation T X tailIndex s)]=ᵐ[P]
      (fun _ => ∫ u in s.val..t.val,∑ k,E (tailIndex i) k u*E (tailIndex j) k u) := by
  letI : MeasurableSpace Ω := m
  let A := fun u => matrixOperatorMap (finiteBlocks (F u) 0 (L u) (0 : Matrix (Fin r) (Fin r) ℝ))
  have hA : Continuous A := matrixOperatorMap.continuous.comp
    (finiteBlocks_continuous F _ L _ hF continuous_const hL continuous_const)
  obtain ⟨Z,hZ,he⟩ := h.product_increments P B A hA E hE ξ hξ hξg.memLp_two T hT N X
  have hH := h.path_information_le P B A E ξ T hT N X tailIndex s
  obtain ⟨hZt,hZs,hZc⟩ := stopped_martingale_conditional_increment_zero P B.F B.le
    (Z (tailIndex i) (tailIndex j)) T s.val t.val hst t.property.2 (hZ _ _) _ hH
  have hi k l : Integrable (fun w => ∫ u in s.val..t.val,
      X w (projIcc 0 T hT u) (tailIndex l)*(A u (X w (projIcc 0 T hT u))) (tailIndex k)) P := by
    simpa only [intervalIntegral.integral_of_le hst] using
      (quadratic_drift_integrable P T hT X h.measurable h.moment A hA (tailIndex k) (tailIndex l) s t).integral_prod_left
  apply conditional_product_increment P _ (hH.trans (B.le _)) _ _ _ _ _
    (hi i j) (hi j i) (hZt.sub hZs) (he (tailIndex i) (tailIndex j) s t)
  · exact innovation_integrated_drift_conditional_zero P B F L hF hL E hE ξ hξ hξg hξ0 T hT N X h hind s t hst i j
  · exact innovation_integrated_drift_conditional_zero P B F L hF hL E hE ξ hξ hξg hξ0 T hT N X h hind s t hst j i
  · exact hZc

end Asakura.Chapter10
