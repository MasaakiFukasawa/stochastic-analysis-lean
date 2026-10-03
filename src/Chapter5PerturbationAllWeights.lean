import Chapter5PerturbationActualTimeSup
import Chapter5FiniteEnergyWeights

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

/-- All three perturbation conclusions for every nonnegative weight.
The large auxiliary weight and positive estimate parameters are chosen
in the proof; the result does not impose a large-weight hypothesis. -/
theorem perturbation_actual_all_weights
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
    (C₀ C₁ β ε₀ : ℝ) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (he₀ : 0<ε₀)
    (hβ : 0≤β)
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
        =O[𝓝 0] (fun ε : ℝ => |ε|^(n+1)) ∧
      (fun ε => ⨆ t : Icc (0:ℝ) R,pointEnergyNorm P
        (fun w => (iter n ε).Y (realTimeClamp t.val) w-(sol ε).Y (realTimeClamp t.val) w))
        =O[𝓝 0] (fun ε : ℝ => |ε|^(n+1)) := by
  let C := C₀+ε₀*C₁
  have hC : 0≤C := add_nonneg hC₀ (mul_nonneg he₀.le hC₁)
  let γ := β+C*(2+C)+1
  have hg : C*(2+C)<γ := by dsimp only [γ]; linarith
  have hγ : 0≤γ := (mul_nonneg hC (by positivity)).trans hg.le
  obtain ⟨mu,ell,hmu,hell,hgap,hparam⟩ := perturbation_positive_parameters C γ hC hg
  have hp := perturbation_actual_family_bigO P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hclock
    R hR hRT sol base iter hiter0 f₀ f₁ hfm₀ hfm₁ hf₀ hf₁ C₀ C₁ γ ell mu ε₀ hC₀ hC₁ he₀ hell hmu hgap hparam hl₀ hl₁ hsol hbase hstep hterm
  have ht := perturbation_actual_uniform_time_bigO P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc hclock
    R hR hRT sol base iter hiter0 f₀ f₁ hfm₀ hfm₁ hf₀ hf₁ C₀ C₁ γ ell mu ε₀ hC₀ hC₁ he₀ hell hmu hgap hparam hl₀ hl₁ hsol hbase hstep hterm
  intro n
  refine ⟨?_,?_,ht n⟩
  · exact finite_energy_bigO_change_weight P R β γ hR hβ hγ _
      (fun ε => (iter n ε).measurableY.sub (sol ε).measurableY)
      (fun ε => (iter n ε).energyY.sub (sol ε).energyY) (n+1) (hp n).1
  · exact finite_energy_bigO_change_weight P R β γ hR hβ hγ _
      (fun ε => (iter n ε).measurableZ.sub (sol ε).measurableZ)
      (fun ε => (iter n ε).energyZ.sub (sol ε).energyZ) (n+1) (hp n).2

end Asakura.Chapter5
