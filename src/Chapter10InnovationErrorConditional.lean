import Chapter10PathInformation
import Chapter10InnovationMartingale
import Chapter10ContinuousStateLaw

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter9
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Actual centered Gaussian error has conditional mean zero given any
earlier completed innovation history. -/
theorem innovation_history_error_conditional_zero {Ω : Type*} [m : MeasurableSpace Ω]
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
    (s u : Icc (0:ℝ) T) (hsu : s.val≤u.val) (i : Fin d) :
    P[(fun w => X w u (headIndex i))|
      nullAugmentedInformation (m := m) P (pathInformation T X tailIndex s)]=ᵐ[P]
      (fun _ => (0:ℝ)) := by
  letI : MeasurableSpace Ω := m
  let A := fun u => matrixOperatorMap (finiteBlocks (F u) 0 (L u) (0 : Matrix (Fin r) (Fin r) ℝ))
  have hA : Continuous A := matrixOperatorMap.continuous.comp
    (finiteBlocks_continuous F _ L _ hF continuous_const hL continuous_const)
  obtain ⟨hg,hmean⟩ := h.centered_gaussian P B A hA E hE ξ hξ hξg hξ0 T hT N X
  let H := nullAugmentedInformation (m := m) P (pathInformation T X tailIndex s)
  letI : MeasurableSpace Ω := m
  have hH := h.path_information_le (m := m) P B A E ξ T hT N X tailIndex s
  let e := fun w k => X w u (headIndex k)
  have hem : Measurable[m] e := Measurable.of_eval (fun k =>
    (measurable_pi_apply _).comp ((continuous_eval_const _).measurable.comp h.measurable))
  have hraw := indep_of_indep_of_le_right (hind u) (path_information_mono T X tailIndex s u hsu)
  have hrle : pathInformation T X tailIndex s≤m :=
    (null_augmented_contains (m := m) P _).trans (hH.trans (B.le _))
  have hindH := independent_completed_history (m := m) P _ _ hem.comap_le hrle hraw
  have heG : Measurable[MeasurableSpace.comap e inferInstance] e := Measurable.of_comap_le le_rfl
  have hc := condExp_indep_eq hem.comap_le (hH.trans (B.le _))
    (((measurable_pi_apply i).comp heG).stronglyMeasurable) hindH
  have hz : (∫ w,X w u (headIndex i) ∂P)=0 := by
    have hi := (hg.map (ContinuousMap.evalCLM ℝ u)).integrable
    have hh := (show (Fin (d+r) → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj (headIndex i)).integral_comp_comm hi
    change (∫ w,X w u (headIndex i) ∂P)=(∫ w,X w u ∂P) (headIndex i) at hh
    rw [hh,hmean]
    rfl
  simpa only [e,Function.comp_def,hz] using! hc

end Asakura.Chapter10
