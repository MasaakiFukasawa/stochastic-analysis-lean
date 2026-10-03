import Chapter10InnovationProductIncrement
import Chapter10InnovationNaturalMartingale
import Chapter10FiniteInnovationCovariation
import Chapter10CompensatedConditionalProduct
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
theorem actual_innovation_covariation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r n : ℕ} (B : BrownianSystem P n)
    (F : ℝ → Matrix (Fin d) (Fin d) ℝ) (L : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (hF : Continuous F) (hL : Continuous L)
    (E : Fin (d+r) → Fin n → ℝ → ℝ) (hE : ∀ i j,Continuous (E i j))
    (ξ : Ω → Fin (d+r) → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (hξ0 : ∫ w,ξ w ∂P=0)
    (T : ℝ) (hT : 0<T) [Fact (0≤(T:EReal))] (N : Fin (d+r) → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin (d+r) → ℝ))
    (h : LinearStateWitness P B
      (fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))) E ξ T hT.le N X)
    (hind : ∀ t : Icc (0:ℝ) T,IndepFun (fun w i => X w t (headIndex i))
      (fun w (z : {u : Icc (0:ℝ) T // u.val≤t.val} × Fin r) => X w z.1.val (tailIndex z.2)) P)
    (hξI : ∀ j,(fun w => ξ w (tailIndex j))=ᵐ[P] 0)
    (hclock : ∀ u i j,(∑ k,E (tailIndex i) k u*E (tailIndex j) k u)=if i=j then 1 else 0) :
    let ρ := finitePrefixTime (T := (T:EReal)) T hT.le
    let H := fun s => nullAugmentedInformation (m := m) P (pathInformation T X tailIndex s)
    (∀ i,LocalMProcessWitness P (fun t => H (ρ t)) (fun t w => X w (ρ t) (tailIndex i))) ∧
      ∀ i j,LocalCovarianceWitness P (fun t => H (ρ t))
        (fun t w => X w (ρ t) (tailIndex i)) (fun t w => X w (ρ t) (tailIndex j))
        (fun t _ => if i=j then (ρ t).val else 0) := by
  letI : MeasurableSpace Ω := m
  let A := fun u => matrixOperatorMap (finiteBlocks (F u) 0 (L u) (0 : Matrix (Fin r) (Fin r) ℝ))
  have hA : Continuous A := matrixOperatorMap.continuous.comp
    (finiteBlocks_continuous F _ L _ hF continuous_const hL continuous_const)
  have hH s := h.path_information_le P B A E ξ T hT.le N X tailIndex s
  obtain ⟨hg,hmean⟩ := h.centered_gaussian P B A hA E hE ξ hξ hξg hξ0 T hT.le N X
  let Y := fun w => ContinuousLinearMap.compLeftContinuous ℝ (Icc (0:ℝ) T)
    (coordinateProjection (tailIndex (d := d) (r := r))) (X w)
  let H := fun s => nullAugmentedInformation (m := m) P (pathInformation T X tailIndex s)
  letI : MeasurableSpace Ω := m
  have hYm s i : Measurable[H s] (fun w => Y w s i) :=
    (path_information_current T X tailIndex s i).mono (null_augmented_contains P _) le_rfl
  have hYi s i := h.coordinate_memLp P B A E ξ T hT.le N X s (tailIndex i)
  have hYg s i : HasGaussianLaw (fun w => Y w s i) P := by
    exact (hg.map (ContinuousMap.evalCLM ℝ s)).map (ContinuousLinearMap.proj (tailIndex i))
  have hYM s t (hst : s≤t) i : P[(fun w => Y w t i)|H s]=ᵐ[P] fun w => Y w s i :=
    innovation_natural_martingale P B F L hF hL E hE ξ hξ hξg hξ0 T hT.le N X h hind s t hst i
  have hYQ s t (hst : s≤t) i j :
      P[(fun w => Y w t i*Y w t j-(if i=j then t.val else 0))|H s]=ᵐ[P]
        fun w => Y w s i*Y w s j-(if i=j then s.val else 0) := by
    have he := innovation_product_conditional_increment P B F L hF hL E hE ξ hξ hξg hξ0
      T hT.le N X h hind s t hst i j
    have hc : (∫ u in s.val..t.val,∑ k,E (tailIndex i) k u*E (tailIndex j) k u)=
        (if i=j then t.val else 0)-(if i=j then s.val else 0) := by
      simp only [hclock,intervalIntegral.integral_const,smul_eq_mul]
      by_cases hij : i=j <;> simp [hij]
    rw [hc] at he
    exact compensated_conditional_product P (H s) ((hH s).trans (B.le _)) _ _
      ((hYi t i).integrable_mul (hYi t j)) ((hYi s i).integrable_mul (hYi s j))
      ((hYm s i).mul (hYm s j)) _ _ he
  have hY0 i : (fun w => Y w ⟨0,le_rfl,hT.le⟩ i)=ᵐ[P] 0 := by
    obtain ⟨Z,hinit,_,_⟩ := h.products P B A hA E hE ξ hξ hξg.memLp_two T hT.le N X
    filter_upwards [hinit,hξI i] with w hw hi
    change X w ⟨0,le_rfl,hT.le⟩ (tailIndex i)=0
    rw [hw]
    exact hi
  exact finite_innovation_covariation P T hT Y H
    (fun s t hst => null_augmented_mono P _ _ (path_information_mono T X tailIndex s t hst))
    (fun s => (hH s).trans (B.le _)) hYm hYg hYM hYQ hY0

end Asakura.Chapter10
