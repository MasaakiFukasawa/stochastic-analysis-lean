import Chapter12BrownianCompactCommonLaw
import Chapter12FiniteBrownianPathMoments
import Chapter7NaturalBrownianSystem

open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter12
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

noncomputable def coordinateBrownianSystem {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (j : Fin d) : BrownianSystem P 1 where
  F := B.F
  mono := B.mono
  le := B.le
  null := B.null
  W := fun _ => B.W j
  C := fun _ _ => B.C j j
  martingale := fun _ => B.martingale j
  cov := fun _ _ => B.cov j j
  clock := by
    intro i k w r hr
    simpa only [Subsingleton.elim i k, if_true] using B.diagonal_clock j w r hr

/-- The continuous local-martingale definition of a Brownian system implies
 the standard finite-dimensional Brownian laws for every coordinate. -/
theorem brownian_system_preBrownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (j : Fin d) : IsPreBrownianReal (fun t : ℝ≥0 => B.W j (realTimeClamp t)) P := by
  obtain ⟨Ω',m',Q,hQ,X,hXm,hXc,hX,_⟩ := Asakura.brownian_motion_exists
  letI := m'
  letI := hQ
  let C := naturalBrownianSystem Q X hX.toIsPreBrownianReal hXm hXc
  have hlaw := brownian_vector_path_common_law P Q (coordinateBrownianSystem B j) C
  constructor
  intro I
  let ev : (Fin 1 → C(ℝ≥0,ℝ)) → (I → ℝ) := fun f t => f 0 t.val
  have hm : Measurable ev := Measurable.of_eval (fun t =>
    (ContinuousMap.measurable_eval t.val).comp (measurable_pi_apply 0))
  have he : (fun w => ev (fun i => brownianCoordinatePath C i w)) =
      (fun w => I.restrict (X · w)) := by
    funext w t
    change X (halfTimeReal (realTimeClamp t.val)) w = X t.val w
    congr 1
    exact Subtype.ext (changed_time_real t.val t.val.property)
  have hi := hlaw.comp hm
  simp only [Function.comp_def] at hi
  rw [he] at hi
  exact hi.symm.hasLaw (hX.hasLaw I)

/-- All finite moments of the compact continuous path are consequences of
 the Brownian driver, not additional assumptions on the SDE. -/
theorem brownian_system_path_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (T : ℝ) (hT : 0 ≤ T) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (brownianSystemCompactPath B T) p P := by
  let X := fun i (t : ℝ≥0) => B.W i (realTimeClamp t)
  have hm i t : Measurable (X i t) :=
    ((B.martingale i).adapted P B.F _ (changed_time_finite t t.property)).mono (B.le _) le_rfl
  have hc i w : Continuous (fun t => X i t w) := (brownianCoordinatePath B i w).continuous
  exact finite_brownian_path_memLp P X (brownian_system_preBrownian P B) hm hc ⟨T,hT⟩ p hp

#print axioms brownian_system_preBrownian
#print axioms brownian_system_path_memLp
end Asakura.EndToEnd
