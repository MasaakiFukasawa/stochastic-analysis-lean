import Chapter5PerturbationEnergyConstructed
import Chapter5PerturbedGenerator

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

/-- The zeroth perturbation error follows from the actual two-solution
a-priori theorem with constants uniform for |epsilon| <= epsilon0. -/
theorem perturbation_base_actual_estimate
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
    (sol base : BSDEFiniteEnergyData P F W c R)
    (f₀ f₁ : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm₀ : Measurable f₀) (hfm₁ : Measurable f₁)
    (hf₀ : MemLp (fun z => f₀ (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hf₁ : MemLp (fun z => f₁ (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C₀ C₁ β ell mu2 ε ε₀ : ℝ) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (he : |ε|≤ε₀)
    (hell : C₀+ε₀*C₁<ell) (hmu2 : 0<mu2) (hβ : (C₀+ε₀*C₁)*(2+ell)+mu2≤β)
    (hl₀ : ∀ z y₁ z₁ y₂ z₂,|f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|≤C₀*(|y₁-y₂|+|z₁-z₂|))
    (hl₁ : ∀ z y₁ z₁ y₂ z₂,|f₁ (z,y₁,z₁)-f₁ (z,y₂,z₂)|≤C₁*(|y₁-y₂|+|z₁-z₂|))
    (hsol : ∀ w r,r∈Icc 0 R → sol.B (w,r)=
      -(f₀ ((w,r),sol.Y (realTimeClamp r) w,sol.Z (w,r))+ε*f₁ ((w,r),sol.Y (realTimeClamp r) w,sol.Z (w,r))))
    (hbase : ∀ w r,r∈Icc 0 R → base.B (w,r)= -f₀ ((w,r),base.Y (realTimeClamp r) w,base.Z (w,r)))
    (hterm : sol.Y (realTimeClamp R) =ᵐ[P] base.Y (realTimeClamp R)) :
    let D := fun z => f₁ (z,base.Y (realTimeClamp z.2) z.1,base.Z z)
    let K := ε^2*(∫ w,(∫ r in 0..R,Real.exp (β*r)*D (w,r)^2) ∂P)/mu2
    (∀ t∈Icc 0 R,(∫ w,Real.exp (β*t)*(sol.Y (realTimeClamp t) w-base.Y (realTimeClamp t) w)^2 ∂P)≤K) ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*(sol.Y (realTimeClamp r) w-base.Y (realTimeClamp r) w)^2) ∂P)≤R*K ∧
    (∫ w,(∫ r in 0..R,Real.exp (β*r)*(sol.Z (w,r)-base.Z (w,r))^2) ∂P)≤ell/(ell-(C₀+ε₀*C₁))*K := by
  dsimp only
  let g := fun p : (Ω × ℝ) × (ℝ × ℝ) => f₀ p+ε*f₁ p
  have hgm : Measurable g := hfm₀.add (hfm₁.const_mul ε)
  have hg0 : MemLp (fun z => g (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))) := hf₀.add (hf₁.const_smul ε)
  have hC : 0≤C₀+ε₀*C₁ := add_nonneg hC₀ (mul_nonneg ((abs_nonneg ε).trans he) hC₁)
  apply bsde_perturbation_energy_constructed P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hclock
    R hR hRT sol base g hgm hg0 (C₀+ε₀*C₁) β ell mu2 hC hell hmu2 hβ
    (perturbed_generator_lipschitz f₀ f₁ C₀ C₁ ε ε₀ hC₀ hC₁ he hl₀ hl₁) hsol ε (fun z => f₁ (z,base.Y (realTimeClamp z.2) z.1,base.Z z)) hterm
  intro w r hr
  dsimp only [g]
  rw [hbase w r hr]
  ring

end Asakura.Chapter5
