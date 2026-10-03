import Chapter10InnovationDriftCancellation
import Chapter10QuadraticDriftIntegrable
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
theorem innovation_integrated_drift_conditional_zero {Ω : Type*} [m : MeasurableSpace Ω]
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
    let A := fun u => matrixOperatorMap (finiteBlocks (F u) 0 (L u) (0 : Matrix (Fin r) (Fin r) ℝ))
    P[(fun w => ∫ u in s.val..t.val,X w (projIcc 0 T hT u) (tailIndex j)*
      (A u (X w (projIcc 0 T hT u))) (tailIndex i))|
      nullAugmentedInformation (m := m) P (pathInformation T X tailIndex s)]=ᵐ[P]
      (fun _ => (0:ℝ)) := by
  letI : MeasurableSpace Ω := m
  dsimp only
  let A := fun u => matrixOperatorMap (finiteBlocks (F u) 0 (L u) (0 : Matrix (Fin r) (Fin r) ℝ))
  have hA : Continuous A := matrixOperatorMap.continuous.comp
    (finiteBlocks_continuous F _ L _ hF continuous_const hL continuous_const)
  have hi := quadratic_drift_integrable P T hT X h.measurable h.moment A hA (tailIndex i) (tailIndex j) s t
  have hh := Asakura.Chapter7.conditional_integral_mean P (volume.restrict (Ioc s.val t.val))
    (fun z : Ω × ℝ => X z.1 (projIcc 0 T hT z.2) (tailIndex j)*
      (A z.2 (X z.1 (projIcc 0 T hT z.2))) (tailIndex i)) hi (fun _ => (0:ℝ))
    (nullAugmentedInformation (m := m) P (pathInformation T X tailIndex s))
    ((h.path_information_le P B A E ξ T hT N X tailIndex s).trans (B.le _))
  have hz : ∀ᵐ u ∂volume.restrict (Ioc s.val t.val),
      P[(fun w => X w (projIcc 0 T hT u) (tailIndex j)*
        (A u (X w (projIcc 0 T hT u))) (tailIndex i))|
        nullAugmentedInformation (m := m) P (pathInformation T X tailIndex s)]=ᵐ[P] (fun _ => (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have huT : u∈Icc (0:ℝ) T := ⟨s.property.1.trans hu.1.le,hu.2.trans t.property.2⟩
    have hp : projIcc 0 T hT u=⟨u,huT⟩ := Subtype.ext (by simp [projIcc,huT.1,huT.2])
    have he := innovation_quadratic_drift_conditional_zero P B F L hF hL E hE ξ hξ hξg hξ0
      T hT N X h hind s ⟨u,huT⟩ hu.1.le i j
    simpa only [A,hp,finiteBlocks_tail_action] using he
  simpa only [intervalIntegral.integral_of_le hst,integral_zero] using hh hz

end Asakura.Chapter10
