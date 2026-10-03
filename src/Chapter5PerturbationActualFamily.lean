import Chapter5PerturbationBaseActual
import Chapter5PerturbationIterationActual
import Chapter5ActualNormCoefficients
import Chapter5BSDEGeneratorNorm
import Chapter5PerturbationPair

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-- The actual sequence of BSDE solutions has the stated perturbation
order. The base and recurrence estimates come from the constructed Ito
a-priori theorem, rather than being supplied as numerical hypotheses. -/
theorem perturbation_actual_family_bigO
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
    (sol : ℝ → BSDEFiniteEnergyData P F W c R)
    (base : BSDEFiniteEnergyData P F W c R)
    (iter : ℕ → ℝ → BSDEFiniteEnergyData P F W c R)
    (hiter0 : ∀ ε,iter 0 ε=base)
    (f₀ f₁ : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm₀ : Measurable f₀) (hfm₁ : Measurable f₁)
    (hf₀ : MemLp (fun z => f₀ (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hf₁ : MemLp (fun z => f₁ (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C₀ C₁ β ell mu ε₀ : ℝ) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (he₀ : 0<ε₀)
    (hell : 0<ell) (hmu : 0<mu) (hgap : C₀+ε₀*C₁<ell^2)
    (hβ : (C₀+ε₀*C₁)*(2+ell^2)+mu^2≤β)
    (hl₀ : ∀ z y₁ z₁ y₂ z₂,|f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|≤C₀*(|y₁-y₂|+|z₁-z₂|))
    (hl₁ : ∀ z y₁ z₁ y₂ z₂,|f₁ (z,y₁,z₁)-f₁ (z,y₂,z₂)|≤C₁*(|y₁-y₂|+|z₁-z₂|))
    (hsol : ∀ ε,|ε|≤ε₀ → ∀ w r,r∈Icc 0 R → (sol ε).B (w,r)=
      -(f₀ ((w,r),(sol ε).Y (realTimeClamp r) w,(sol ε).Z (w,r))+ε*f₁ ((w,r),(sol ε).Y (realTimeClamp r) w,(sol ε).Z (w,r))))
    (hbase : ∀ w r,r∈Icc 0 R → base.B (w,r)= -f₀ ((w,r),base.Y (realTimeClamp r) w,base.Z (w,r)))
    (hstep : ∀ n ε,|ε|≤ε₀ → ∀ w r,r∈Icc 0 R → (iter (n+1) ε).B (w,r)=
      -(f₀ ((w,r),(iter (n+1) ε).Y (realTimeClamp r) w,(iter (n+1) ε).Z (w,r))+
        ε*f₁ ((w,r),(iter n ε).Y (realTimeClamp r) w,(iter n ε).Z (w,r))))
    (hterm : ∀ n ε,|ε|≤ε₀ → (iter n ε).Y (realTimeClamp R) =ᵐ[P] (sol ε).Y (realTimeClamp R)) :
    ∀ n,
      (fun ε => finiteEnergyNorm P R β (fun z => (iter n ε).Y (realTimeClamp z.2) z.1-(sol ε).Y (realTimeClamp z.2) z.1))
        =O[𝓝 0] (fun ε : ℝ => |ε|^(n+1)) ∧
      (fun ε => finiteEnergyNorm P R β (fun z => (iter n ε).Z z-(sol ε).Z z))
        =O[𝓝 0] (fun ε : ℝ => |ε|^(n+1)) := by
  let C := C₀+ε₀*C₁
  have hC : 0≤C := add_nonneg hC₀ (mul_nonneg he₀.le hC₁)
  have hC₀C : C₀≤C := le_add_of_nonneg_right (mul_nonneg he₀.le hC₁)
  have hβ0 : 0≤β := (add_nonneg (mul_nonneg hC (by positivity)) (sq_nonneg mu)).trans hβ
  have hl₀C z y₁ z₁ y₂ z₂ : |f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|≤C*(|y₁-y₂|+|z₁-z₂|) :=
    (hl₀ z y₁ z₁ y₂ z₂).trans (mul_le_mul_of_nonneg_right hC₀C (by positivity))
  let EY := fun n ε => finiteEnergyNorm P R β (fun z => (iter n ε).Y (realTimeClamp z.2) z.1-(sol ε).Y (realTimeClamp z.2) z.1)
  let EZ := fun n ε => finiteEnergyNorm P R β (fun z => (iter n ε).Z z-(sol ε).Z z)
  let D := finiteEnergyNorm P R β (fun z => f₁ (z,base.Y (realTimeClamp z.2) z.1,base.Z z))
  let a := Real.sqrt R/mu
  let b := ell/(mu*Real.sqrt (ell^2-C))
  have ha : 0≤a := by positivity
  have hb : 0≤b := by positivity
  have hbaseN ε (he : |ε|≤ε₀) : EY 0 ε≤a*D*|ε| ∧ EZ 0 ε≤b*D*|ε| := by
    have ht : (sol ε).Y (realTimeClamp R) =ᵐ[P] base.Y (realTimeClamp R) := by
      simpa only [hiter0] using (hterm 0 ε he).symm
    have hh := perturbation_base_actual_estimate P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hclock
      R hR hRT (sol ε) base f₀ f₁ hfm₀ hfm₁ hf₀ hf₁ C₀ C₁ β (ell^2) (mu^2) ε ε₀ hC₀ hC₁ he
      hgap (sq_pos_of_pos hmu) hβ hl₀ hl₁ (hsol ε he) hbase ht
    dsimp only at hh
    obtain ⟨hy,hz⟩ := actual_energy_norm_coefficients P R C β ell mu ε hR hell hgap hmu
      (fun z => (sol ε).Y (realTimeClamp z.2) z.1-base.Y (realTimeClamp z.2) z.1)
      (fun z => (sol ε).Z z-base.Z z)
      (fun z => f₁ (z,base.Y (realTimeClamp z.2) z.1,base.Z z)) hh.2.1 hh.2.2
    rw [finiteEnergyNorm_sub_comm P R β (fun z => (sol ε).Y (realTimeClamp z.2) z.1) (fun z => base.Y (realTimeClamp z.2) z.1)] at hy
    rw [finiteEnergyNorm_sub_comm P R β (sol ε).Z base.Z] at hz
    dsimp only [EY,EZ]
    rw [hiter0]
    constructor
    · convert hy using 1 <;> dsimp only [a,D] <;> ring
    · convert hz using 1 <;> dsimp only [b,D] <;> ring
  have hstepN n ε (he : |ε|≤ε₀) :
      EY (n+1) ε≤a*C₁*|ε| *(EY n ε+EZ n ε) ∧ EZ (n+1) ε≤b*C₁*|ε| *(EY n ε+EZ n ε) := by
    have hh := perturbation_iteration_actual_estimate P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hclock
      R hR hRT (iter (n+1) ε) (iter n ε) (sol ε) f₀ f₁ hfm₀ hfm₁ hf₀ hf₁ C C₁ β (ell^2) (mu^2) ε hC hC₁
      hgap (sq_pos_of_pos hmu) hβ hl₀C hl₁ (hstep n ε he) (hsol ε he) (hterm (n+1) ε he)
    dsimp only at hh
    obtain ⟨hy,hz⟩ := actual_energy_norm_coefficients P R C β ell mu ε hR hell hgap hmu
      (fun z => (iter (n+1) ε).Y (realTimeClamp z.2) z.1-(sol ε).Y (realTimeClamp z.2) z.1)
      (fun z => (iter (n+1) ε).Z z-(sol ε).Z z)
      (fun z => f₁ (z,(iter n ε).Y (realTimeClamp z.2) z.1,(iter n ε).Z z)-f₁ (z,(sol ε).Y (realTimeClamp z.2) z.1,(sol ε).Z z)) hh.2.1 hh.2.2
    have hd := bsde_generator_difference_norm P F W c R β hR hβ0 (iter n ε) (sol ε) f₁ hfm₁ hf₁ C₁ hC₁ hl₁
    constructor
    · calc
        EY (n+1) ε ≤ |ε| *a*finiteEnergyNorm P R β (fun z => f₁ (z,(iter n ε).Y (realTimeClamp z.2) z.1,(iter n ε).Z z)-f₁ (z,(sol ε).Y (realTimeClamp z.2) z.1,(sol ε).Z z)) := hy
        _ ≤ |ε| *a*(C₁*(EY n ε+EZ n ε)) := mul_le_mul_of_nonneg_left hd (by positivity)
        _ = _ := by ring
    · calc
        EZ (n+1) ε ≤ |ε| *b*finiteEnergyNorm P R β (fun z => f₁ (z,(iter n ε).Y (realTimeClamp z.2) z.1,(iter n ε).Z z)-f₁ (z,(sol ε).Y (realTimeClamp z.2) z.1,(sol ε).Z z)) := hz
        _ ≤ |ε| *b*(C₁*(EY n ε+EZ n ε)) := mul_le_mul_of_nonneg_left hd (by positivity)
        _ = _ := by ring
  exact (perturbation_pair_bigO EY EZ a b C₁ D ε₀ ha hb hC₁ (finiteEnergyNorm_nonneg _ _ _ _) he₀
    (fun _ _ => finiteEnergyNorm_nonneg _ _ _ _) (fun _ _ => finiteEnergyNorm_nonneg _ _ _ _)
    (fun ε he => (hbaseN ε he).1) (fun ε he => (hbaseN ε he).2)
    (fun n ε he => (hstepN n ε he).1) (fun n ε he => (hstepN n ε he).2)).2

end Asakura.Chapter5
