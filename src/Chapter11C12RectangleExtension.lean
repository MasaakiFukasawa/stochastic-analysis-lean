import Chapter11IntervalRetraction
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set Filter Function
open scoped Topology
namespace Asakura.Chapter11
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Local C1,2 regularity suffices: smooth retractions extend the function
from an open rectangle, preserving it near the closed stopping rectangle.
There is no assumption on the second time derivative. -/
theorem c12_rectangle_extension
    (a t0 t1 b l x0 x1 u : ℝ)
    (hat : a<t0) (htt : t0≤t1) (htb : t1<b)
    (hlx : l<x0) (hxx : x0≤x1) (hxu : x1<u)
    (v : ℝ → ℝ → ℝ) (vt : ℝ × ℝ → ℝ)
    (hv : ∀ t∈Ioo a b,ContDiffOn ℝ 2 (v t) (Ioo l u))
    (hvt : ∀ t∈Ioo a b,∀ x∈Ioo l u,HasDerivAt (fun s => v s x) (vt (t,x)) t)
    (hvc : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (Ioo a b ×ˢ Ioo l u))
    (hvtc : ContinuousOn vt (Ioo a b ×ˢ Ioo l u))
    (hdxc : ContinuousOn (fun z : ℝ × ℝ => deriv (v z.1) z.2) (Ioo a b ×ˢ Ioo l u))
    (hxxc : ContinuousOn (fun z : ℝ × ℝ => deriv (deriv (v z.1)) z.2) (Ioo a b ×ˢ Ioo l u)) :
    ∃ g : ℝ → ℝ → ℝ,∃ gt : ℝ × ℝ → ℝ,
      (∀ t,ContDiff ℝ 2 (g t)) ∧
      (∀ t x,HasDerivAt (fun s => g s x) (gt (t,x)) t) ∧
      Continuous (fun z : ℝ × ℝ => g z.1 z.2) ∧ Continuous gt ∧
      Continuous (fun z : ℝ × ℝ => deriv (g z.1) z.2) ∧
      Continuous (fun z : ℝ × ℝ => deriv (deriv (g z.1)) z.2) ∧
      ∀ t∈Icc t0 t1,∀ x∈Icc x0 x1,
        (fun z : ℝ × ℝ => g z.1 z.2)=ᶠ[𝓝 (t,x)] (fun z => v z.1 z.2) ∧ gt (t,x)=vt (t,x) := by
  obtain ⟨ρ,hρ,hρmem,hρeq⟩ := interval_smooth_retraction a t0 t1 b hat htt htb
  obtain ⟨ζ,hζ,hζmem,hζeq⟩ := interval_smooth_retraction l x0 x1 u hlx hxx hxu
  let g := fun t x => v (ρ t) (ζ x)
  let gt := fun z : ℝ × ℝ => vt (ρ z.1,ζ z.2)*deriv ρ z.1
  have hmap : Continuous (fun z : ℝ × ℝ => (ρ z.1,ζ z.2)) :=
    (hρ.continuous.comp continuous_fst).prodMk (hζ.continuous.comp continuous_snd)
  have hmem (z : ℝ × ℝ) : (ρ z.1,ζ z.2)∈Ioo a b ×ˢ Ioo l u := ⟨hρmem _,hζmem _⟩
  have hvs t x : ContDiffAt ℝ 2 (v (ρ t)) (ζ x) :=
    (hv _ (hρmem _)).contDiffAt (isOpen_Ioo.mem_nhds (hζmem _))
  have hgs t : ContDiff ℝ 2 (g t) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hvs t x).comp x hζ.contDiffAt
  have hgrad t x : deriv (g t) x=deriv (v (ρ t)) (ζ x)*deriv ζ x :=
    (((hvs t x).differentiableAt (by norm_num)).hasDerivAt.comp x
      ((hζ.differentiable (by norm_num)).differentiableAt.hasDerivAt)).deriv
  have hsecond t x : deriv (deriv (g t)) x=
      deriv (deriv (v (ρ t))) (ζ x)*(deriv ζ x)^2+deriv (v (ρ t)) (ζ x)*deriv (deriv ζ) x := by
    have hdv : DifferentiableAt ℝ (deriv (v (ρ t))) (ζ x) :=
      (((hv _ (hρmem _)).deriv_of_isOpen isOpen_Ioo (by norm_num : (1:WithTop ℕ∞)+1≤2)).contDiffAt
        (isOpen_Ioo.mem_nhds (hζmem _))).differentiableAt (by norm_num)
    have hd := (hdv.hasDerivAt.comp x ((hζ.differentiable (by norm_num)).differentiableAt.hasDerivAt)).mul
      ((hζ.differentiable_deriv_two).differentiableAt.hasDerivAt)
    change HasDerivAt (fun y => deriv (v (ρ t)) (ζ y)*deriv ζ y) _ x at hd
    simp only [Function.comp_def] at hd
    have he : deriv (g t)=fun y => deriv (v (ρ t)) (ζ y)*deriv ζ y := funext (hgrad t)
    rw [he]
    change deriv (fun y => deriv (v (ρ t)) (ζ y)*deriv ζ y) x=_
    rw [hd.deriv]
    ring
  have hζdc : Continuous (deriv ζ) := hζ.continuous_deriv (by norm_num)
  have hζddc : Continuous (deriv (deriv ζ)) := (ContDiff.deriv' (n:=1) hζ).continuous_deriv (by norm_num)
  refine ⟨g,gt,hgs,?_,hvc.comp_continuous hmap hmem,?_,?_,?_,?_⟩
  · intro t x
    exact (hvt _ (hρmem _) _ (hζmem _)).comp t ((hρ.differentiable (by norm_num)).differentiableAt.hasDerivAt)
  · exact (hvtc.comp_continuous hmap hmem).mul ((hρ.continuous_deriv (by norm_num)).comp continuous_fst)
  · simp_rw [hgrad]
    exact (hdxc.comp_continuous hmap hmem).mul (hζdc.comp continuous_snd)
  · simp_rw [hsecond]
    exact ((hxxc.comp_continuous hmap hmem).mul ((hζdc.comp continuous_snd).pow 2)).add
      ((hdxc.comp_continuous hmap hmem).mul (hζddc.comp continuous_snd))
  · intro t ht x hx
    have ht0 : ρ t=t := (hρeq t ht).eq_of_nhds
    have hx0 : ζ x=x := (hζeq x hx).eq_of_nhds
    have ht1 : deriv ρ t=1 := by rw [(hρeq t ht).deriv_eq,deriv_id]
    constructor
    · filter_upwards [(hρeq t ht).comp_tendsto continuous_fst.continuousAt.tendsto,
        (hζeq x hx).comp_tendsto continuous_snd.continuousAt.tendsto] with z hzt hzx
      change v (ρ z.1) (ζ z.2)=v z.1 z.2
      change ρ z.1=z.1 at hzt
      change ζ z.2=z.2 at hzx
      rw [hzt,hzx]
    · dsimp only [gt]
      rw [ht0,hx0,ht1,mul_one]

end Asakura.Chapter11
