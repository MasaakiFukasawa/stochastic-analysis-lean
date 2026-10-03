import Chapter5PerturbationFamiliesConstructed

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 7000000
set_option backward.isDefEq.respectTransparency false

/-- Chapter 5 perturbation theorem: construct actual solutions and iterates,
then derive all three error rates from the actual Ito a-priori estimate. -/
theorem perturbation_existence_and_rates
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W A : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0<c j) (hcm : StrictMono c) (hcT : ∀ j,(c j:EReal)<T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j,realTimeClamp (T := T) (c j)<⊤)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (hco : ∀ r,∃ j,r≤c j)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hFnat : F (realTimeClamp R)=Asakura.nullAugmentation (m := m) P (pastSigma W (realTimeClamp R)))
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 P) (hξm : Measurable[F (realTimeClamp R)] ξ)
    (f₀ f₁ : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm₀ : Measurable f₀) (hfm₁ : Measurable f₁)
    (hfp₀ : ∀ t : Icc (0:ℝ) R,
      @Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
        (fun p : Ω × (Iic t × (ℝ × ℝ)) => f₀ ((p.1,p.2.1.val.val),p.2.2)))
    (hfp₁ : ∀ t : Icc (0:ℝ) R,
      @Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
        (fun p : Ω × (Iic t × (ℝ × ℝ)) => f₁ ((p.1,p.2.1.val.val),p.2.2)))
    (hf₀ : MemLp (fun z => f₀ (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hf₁ : MemLp (fun z => f₁ (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C₀ C₁ : ℝ) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁)
    (hl₀ : ∀ z y₁ z₁ y₂ z₂,|f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|≤C₀*(|y₁-y₂|+|z₁-z₂|))
    (hl₁ : ∀ z y₁ z₁ y₂ z₂,|f₁ (z,y₁,z₁)-f₁ (z,y₂,z₂)|≤C₁*(|y₁-y₂|+|z₁-z₂|))
    (β : ℝ) (hβ : 0≤β) :
    ∃ (sol : ℝ → BSDEFiniteEnergyData P F W c R)
      (base : BSDEFiniteEnergyData P F W c R)
      (iter : ℕ → ℝ → BSDEFiniteEnergyData P F W c R),
      (∀ ε,iter 0 ε=base) ∧
      (∀ ε,(sol ε).Y (realTimeClamp R) =ᵐ[P] ξ) ∧
      (∀ n ε,(iter n ε).Y (realTimeClamp R) =ᵐ[P] ξ) ∧
      (∀ ε w r,r∈Icc 0 R → (sol ε).B (w,r)=
        -(f₀ ((w,r),(sol ε).Y (realTimeClamp r) w,(sol ε).Z (w,r))+
          ε*f₁ ((w,r),(sol ε).Y (realTimeClamp r) w,(sol ε).Z (w,r)))) ∧
      (∀ w r,r∈Icc 0 R → base.B (w,r)= -f₀ ((w,r),base.Y (realTimeClamp r) w,base.Z (w,r))) ∧
      (∀ n ε w r,r∈Icc 0 R → (iter (n+1) ε).B (w,r)=
        -(f₀ ((w,r),(iter (n+1) ε).Y (realTimeClamp r) w,(iter (n+1) ε).Z (w,r))+
          ε*f₁ ((w,r),(iter n ε).Y (realTimeClamp r) w,(iter n ε).Z (w,r)))) ∧
    ∀ n,
      (fun ε => finiteEnergyNorm P R β (fun z => (iter n ε).Y (realTimeClamp z.2) z.1-(sol ε).Y (realTimeClamp z.2) z.1))
        =O[𝓝 0] (fun ε : ℝ => |ε|^(n+1)) ∧
      (fun ε => finiteEnergyNorm P R β (fun z => (iter n ε).Z z-(sol ε).Z z))
        =O[𝓝 0] (fun ε : ℝ => |ε|^(n+1)) ∧
      (fun ε => ⨆ t : Icc (0:ℝ) R,pointEnergyNorm P
        (fun w => (iter n ε).Y (realTimeClamp t.val) w-(sol ε).Y (realTimeClamp t.val) w))
        =O[𝓝 0] (fun ε : ℝ => |ε|^(n+1)) := by
  obtain ⟨sol,base,iter,hi0,hst,hit,hsB,hbB,hiB⟩ := perturbation_families_constructed
    P hT F hF hle hnull W A hW hA hclock c hc hcm hcT hct hcut hcc hco R hR hRT hFnat
    ξ hξ hξm f₀ f₁ hfm₀ hfm₁ hfp₀ hfp₁ hf₀ hf₁ C₀ C₁ hC₀ hC₁ hl₀ hl₁
  refine ⟨sol,base,iter,hi0,hst,hit,hsB,hbB,hiB,?_⟩
  exact perturbation_actual_all_weights P hT F hF hle hnull W A hW hA c hc hcm hcT hct hcut hcc
    (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe_iff.mpr hr.2).trans_lt (hcT n)))
    R hR hRT sol base iter hi0 f₀ f₁ hfm₀ hfm₁ hf₀ hf₁ C₀ C₁ β 1 hC₀ hC₁ (by norm_num) hβ
    hl₀ hl₁ (fun ε _ => hsB ε) hbB (fun n ε _ => hiB n ε)
    (fun n ε _ => (hit n ε).trans (hst ε).symm)

end Asakura.Chapter5
