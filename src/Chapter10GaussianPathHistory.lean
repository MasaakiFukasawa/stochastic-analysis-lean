import Chapter10GaussianHistory
import Chapter10FiniteBlockProjection

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter10
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- A Gaussian continuous path and the proved past cross-moment identities
supply independence of the error from the entire innovation history. -/
theorem gaussian_path_error_independent_history {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r : ℕ} (T : ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin (d+r) → ℝ)) (hm : Measurable X) (hg : HasGaussianLaw X P)
    (hzero : ∀ s : Icc (0:ℝ) T,∀ i,(∫ w,X w s i ∂P)=0)
    (hcross : ∀ s t : Icc (0:ℝ) T,s.val≤t.val → ∀ i j,
      (∫ w,X w t (headIndex i)*X w s (tailIndex j) ∂P)=0)
    (t : Icc (0:ℝ) T) :
    IndepFun (fun w i => X w t (headIndex i))
      (fun w (z : {s : Icc (0:ℝ) T // s.val≤t.val} × Fin r) => X w z.1.val (tailIndex z.2)) P := by
  classical
  let ι := {s : Icc (0:ℝ) T // s.val≤t.val} × Fin r
  let e := fun w i => X w t (headIndex i)
  let I := fun z : ι => fun w => X w z.1.val (tailIndex z.2)
  let Le : C(Icc (0:ℝ) T,Fin (d+r) → ℝ) →L[ℝ] (Fin d → ℝ) :=
    (coordinateProjection (headIndex (d := d) (r := r))).comp (ContinuousMap.evalCLM ℝ t)
  let Li := fun z : ι => (show C(Icc (0:ℝ) T,Fin (d+r) → ℝ) →L[ℝ] ℝ from
    (ContinuousLinearMap.proj (tailIndex z.2)).comp (ContinuousMap.evalCLM ℝ z.1.val))
  have he : Measurable e := Le.continuous.measurable.comp hm
  have hI z : Measurable (I z) := (Li z).continuous.measurable.comp hm
  apply gaussian_error_independent_history P e I he hI
  · intro J
    have hh := hg.map (Le.prod (ContinuousLinearMap.pi (fun z : J => Li z.val)))
    exact hh
  · intro i z
    simp only [covariance,e,I,hzero,sub_zero]
    exact hcross z.1.val t z.1.property i z.2

end Asakura.Chapter10
