import Chapter5PerturbationEnergyConstructed
import Chapter5PerturbedGenerator

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

/-- Substitute the actual successive perturbation equations into the
a-priori theorem. The discrepancy is derived as epsilon times the
previous iterate's generator error. -/
theorem perturbation_iteration_actual_estimate
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hA : LocalCovarianceWitness P F W W A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (next prev sol : BSDEFiniteEnergyData P F W c R)
    (f₀ f₁ : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm₀ : Measurable f₀) (hfm₁ : Measurable f₁)
    (hf₀ : MemLp (fun z => f₀ (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hf₁ : MemLp (fun z => f₁ (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C₀ C₁ β ell mu2 ε : ℝ) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁)
    (hell : C₀<ell) (hmu2 : 0<mu2) (hβ : C₀*(2+ell)+mu2≤β)
    (hl₀ : ∀ z y₁ z₁ y₂ z₂,|f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|≤C₀*(|y₁-y₂|+|z₁-z₂|))
    (hl₁ : ∀ z y₁ z₁ y₂ z₂,|f₁ (z,y₁,z₁)-f₁ (z,y₂,z₂)|≤C₁*(|y₁-y₂|+|z₁-z₂|))
    (hnext : ∀ w r,r∈Icc 0 R → next.B (w,r)=
      -(f₀ ((w,r),next.Y (realTimeClamp r) w,next.Z (w,r))+ε*f₁ ((w,r),prev.Y (realTimeClamp r) w,prev.Z (w,r))))
    (hsol : ∀ w r,r∈Icc 0 R → sol.B (w,r)=
      -(f₀ ((w,r),sol.Y (realTimeClamp r) w,sol.Z (w,r))+ε*f₁ ((w,r),sol.Y (realTimeClamp r) w,sol.Z (w,r))))
    (hterm : next.Y (realTimeClamp R) =ᵐ[P] sol.Y (realTimeClamp R)) :
    let D := fun z => f₁ (z,prev.Y (realTimeClamp z.2) z.1,prev.Z z)-f₁ (z,sol.Y (realTimeClamp z.2) z.1,sol.Z z)
    let K := ε^2*(∫ w,(∫ r in 0..R,Real.exp (β*r)*D (w,r)^2) ∂P)/mu2
    (∀ t∈Icc 0 R,(∫ w,Real.exp (β*t)*(next.Y (realTimeClamp t) w-sol.Y (realTimeClamp t) w)^2 ∂P)≤K) ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*(next.Y (realTimeClamp r) w-sol.Y (realTimeClamp r) w)^2) ∂P)≤R*K ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*(next.Z (w,r)-sol.Z (w,r))^2) ∂P)≤ell/(ell-C₀)*K := by
  dsimp only
  let G := fun z => f₁ (z,prev.Y (realTimeClamp z.2) z.1,prev.Z z)
  have hGm : Measurable G := hfm₁.comp (measurable_id.prodMk (prev.measurableY.prodMk prev.measurableZ))
  have hG2 := generator_memLp _ f₁ hfm₁ _ _ prev.measurableY prev.measurableZ prev.energyY prev.energyZ hf₁ C₁ hC₁
    (fun z y z' => by simpa only [sub_zero] using hl₁ z y z' 0 0)
  let g := fun p : (Ω × ℝ) × (ℝ × ℝ) => f₀ p+ε*G p.1
  have hgm : Measurable g := hfm₀.add ((hGm.comp measurable_fst).const_mul ε)
  have hg0 : MemLp (fun z => g (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))) := hf₀.add (hG2.const_smul ε)
  apply bsde_perturbation_energy_constructed P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hclock
    R hR hRT next sol g hgm hg0 C₀ β ell mu2 hC₀ hell hmu2 hβ
    (frozen_perturbed_generator_lipschitz f₀ G C₀ ε hl₀) hnext ε (fun z => f₁ (z,prev.Y (realTimeClamp z.2) z.1,prev.Z z)-f₁ (z,sol.Y (realTimeClamp z.2) z.1,sol.Z z)) hterm
  intro w r hr
  dsimp only [g,G]
  rw [hsol w r hr]
  ring

end Asakura.Chapter5
