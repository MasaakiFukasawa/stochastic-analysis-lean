import Chapter4PositiveTimeExtension
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set Filter Function
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Extend a C1,2 function from positive times to all real times while
preserving its values and all derivatives on [eps,infinity). There is no
extra regularity requirement at time zero. -/
theorem c12_positive_time_extension {dim : ℕ}
    (v : ℝ → (Fin dim → ℝ) → ℝ) (vt : ℝ × (Fin dim → ℝ) → ℝ)
    (hv : ∀ t,0<t → ContDiff ℝ 2 (v t))
    (hvt : ∀ t,0<t → ∀ x,HasDerivAt (fun s => v s x) (vt (t,x)) t)
    (hvc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => v z.1 z.2) {z | 0<z.1})
    (hvtc : ContinuousOn vt {z | 0<z.1})
    (hdxc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (v z.1) z.2) {z | 0<z.1})
    (hhc : ContinuousOn (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (v z.1)) z.2) {z | 0<z.1})
    (eps : ℝ) (heps : 0<eps) :
    ∃ u : ℝ → (Fin dim → ℝ) → ℝ,∃ ut : ℝ × (Fin dim → ℝ) → ℝ,
      (∀ t,ContDiff ℝ 2 (u t)) ∧
      (∀ t x,HasDerivAt (fun s => u s x) (ut (t,x)) t) ∧
      Continuous (fun z : ℝ × (Fin dim → ℝ) => u z.1 z.2) ∧ Continuous ut ∧
      Continuous (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (u z.1) z.2) ∧
      Continuous (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (u z.1)) z.2) ∧
      ∀ t,eps≤t → ∀ x,u t x=v t x ∧ ut (t,x)=vt (t,x) ∧
        fderiv ℝ (u t) x=fderiv ℝ (v t) x ∧
        fderiv ℝ (fderiv ℝ (u t)) x=fderiv ℝ (fderiv ℝ (v t)) x := by
  obtain ⟨ρ,hρ,hρp,hρeq⟩ := positive_time_retraction eps heps
  let u := fun t x => v (ρ t) x
  let ut := fun z : ℝ × (Fin dim → ℝ) => vt (ρ z.1,z.2)*deriv ρ z.1
  have hmap : Continuous (fun z : ℝ × (Fin dim → ℝ) => (ρ z.1,z.2)) :=
    (hρ.continuous.comp continuous_fst).prodMk continuous_snd
  have hmem (z : ℝ × (Fin dim → ℝ)) : (ρ z.1,z.2)∈{z : ℝ × (Fin dim → ℝ) | 0<z.1} := hρp z.1
  refine ⟨u,ut,fun t => hv _ (hρp t),?_,hvc.comp_continuous hmap hmem,?_,
    hdxc.comp_continuous hmap hmem,hhc.comp_continuous hmap hmem,?_⟩
  · intro t x
    exact (hvt _ (hρp t) x).comp t ((hρ.differentiable (by norm_num)).differentiableAt.hasDerivAt)
  · exact (hvtc.comp_continuous hmap hmem).mul ((hρ.continuous_deriv (by norm_num)).comp continuous_fst)
  · intro t ht x
    have he := hρeq t ht
    have he0 : ρ t=t := he.eq_of_nhds
    have he1 : deriv ρ t=1 := by rw [he.deriv_eq,deriv_id]
    dsimp only [u,ut]
    rw [he0,he1,mul_one]
    exact ⟨rfl,rfl,rfl,rfl⟩

end Asakura.Chapter4
