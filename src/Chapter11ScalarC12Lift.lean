import Chapter4C12DensityIto
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set Filter
open scoped Topology
namespace Asakura.Chapter11
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

noncomputable def scalarC12Lift (g : ℝ → ℝ → ℝ) (t : ℝ) (x : Fin 1 → ℝ) : ℝ := g t (x 0)

theorem scalar_c12_lift_first (g : ℝ → ℝ → ℝ) (hg : ∀ t,ContDiff ℝ 2 (g t))
    (t : ℝ) (x : Fin 1 → ℝ) :
    fderiv ℝ (scalarC12Lift g t) x=deriv (g t) (x 0) • (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ) := by
  have hd := ((hg t).differentiable (by norm_num)).differentiableAt.hasDerivAt.comp_hasFDerivAt x
    (hasFDerivAt_apply (𝕜:=ℝ) 0 x)
  change HasFDerivAt (scalarC12Lift g t) _ x at hd
  rw [hd.fderiv]

theorem scalar_c12_lift_second (g : ℝ → ℝ → ℝ) (hg : ∀ t,ContDiff ℝ 2 (g t))
    (t : ℝ) (x : Fin 1 → ℝ) :
    fderiv ℝ (fderiv ℝ (scalarC12Lift g t)) x=
      deriv (deriv (g t)) (x 0) •
        ((ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ)) := by
  have hh := ((hg t).differentiable_deriv_two).differentiableAt.hasDerivAt.comp_hasFDerivAt x
    (hasFDerivAt_apply (𝕜:=ℝ) 0 x)
  have hd := hh.smul_const (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ)
  have he : fderiv ℝ (scalarC12Lift g t)=fun y => deriv (g t) (y 0) •
      (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ) := funext (scalar_c12_lift_first g hg t)
  rw [he]
  change HasFDerivAt (fun y : Fin 1 → ℝ => deriv (g t) (y 0) • (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ)) _ x at hd
  rw [hd.fderiv]
  ext h k
  simp only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

/-- Translate scalar C1,2 data to the one-dimensional vector interface
used by the already proved Ito formula. -/
theorem scalar_c12_lift_regular (g : ℝ → ℝ → ℝ) (gt : ℝ × ℝ → ℝ)
    (hg : ∀ t,ContDiff ℝ 2 (g t))
    (hgt : ∀ t x,HasDerivAt (fun s => g s x) (gt (t,x)) t)
    (hgc : Continuous (fun z : ℝ × ℝ => g z.1 z.2)) (hgtc : Continuous gt)
    (hdc : Continuous (fun z : ℝ × ℝ => deriv (g z.1) z.2))
    (hddc : Continuous (fun z : ℝ × ℝ => deriv (deriv (g z.1)) z.2)) :
    (∀ t,ContDiff ℝ 2 (scalarC12Lift g t)) ∧
    (∀ t x,HasDerivAt (fun s => scalarC12Lift g s x) (gt (t,x 0)) t) ∧
    Continuous (fun z : ℝ × (Fin 1 → ℝ) => scalarC12Lift g z.1 z.2) ∧
    Continuous (fun z : ℝ × (Fin 1 → ℝ) => gt (z.1,z.2 0)) ∧
    Continuous (fun z : ℝ × (Fin 1 → ℝ) => fderiv ℝ (scalarC12Lift g z.1) z.2) ∧
    Continuous (fun z : ℝ × (Fin 1 → ℝ) => fderiv ℝ (fderiv ℝ (scalarC12Lift g z.1)) z.2) := by
  have hmap : Continuous (fun z : ℝ × (Fin 1 → ℝ) => (z.1,z.2 0)) :=
    continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd)
  refine ⟨fun t => (hg t).comp (by fun_prop),fun t x => hgt t (x 0),hgc.comp hmap,hgtc.comp hmap,?_,?_⟩
  · simp_rw [scalar_c12_lift_first g hg]
    exact (hdc.comp hmap).smul continuous_const
  · simp_rw [scalar_c12_lift_second g hg]
    exact (hddc.comp hmap).smul continuous_const

end Asakura.Chapter11
