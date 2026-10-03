import Chapter10GaussianHistory
import Chapter10GaussianIntervalPath
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The Brownian bridge is independent of the terminal value. Gaussianity
is inherited from the continuous Brownian path, and the cross-covariance is
computed explicitly; independence is not postulated. -/
theorem bridge_terminal_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0 < T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X) (hXg : HasGaussianLaw X P)
    (hcov : ∀ s : Icc (0:ℝ) T,
      cov[(fun w => X w ⟨T,hT.le,le_rfl⟩),(fun w => X w s); P] = s.val) :
    IndepFun (fun w => X w ⟨T,hT.le,le_rfl⟩)
      (fun w (s : Icc (0:ℝ) T) => X w s-s.val/T*X w ⟨T,hT.le,le_rfl⟩) P := by
  let t : Icc (0:ℝ) T := ⟨T,hT.le,le_rfl⟩
  let L : C(Icc (0:ℝ) T,ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ t
  let B : Icc (0:ℝ) T → C(Icc (0:ℝ) T,ℝ) →L[ℝ] ℝ := fun s =>
    ContinuousMap.evalCLM ℝ s-(s.val/T) • L
  let Le : C(Icc (0:ℝ) T,ℝ) →L[ℝ] (Fin 1 → ℝ) := ContinuousLinearMap.pi (fun _ => L)
  have he := Asakura.Chapter10.gaussian_error_independent_history P
    (fun w => Le (X w)) (fun s w => B s (X w))
    (Le.continuous.measurable.comp hXm) (fun s => (B s).continuous.measurable.comp hXm)
    (fun J => hXg.map (Le.prod (ContinuousLinearMap.pi (fun s : J => B s.val))))
    (by
      intro i s
      have hL : MemLp (fun w => L (X w)) 2 P := (hXg.map L).memLp (by simp)
      have hs : MemLp (fun w => X w s) 2 P := (hXg.map (ContinuousMap.evalCLM ℝ s)).memLp (by simp)
      change MemLp (fun w => X w t) 2 P at hL
      change cov[(fun w => X w t),(fun w => X w s-s.val/T*X w t);P] = 0
      rw [covariance_fun_sub_right hL hs (hL.const_mul _),covariance_const_mul_right,
        hcov s,hcov t]
      change s.val-s.val/T*T = 0
      rw [div_mul_cancel₀ _ hT.ne',sub_self])
  have hi := he.comp (measurable_pi_apply (0 : Fin 1)) measurable_id
  exact hi

end Asakura.Chapter12
