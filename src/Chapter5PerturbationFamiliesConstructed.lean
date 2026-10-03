import Chapter5PerturbationNextSolution
import Chapter5PerturbationAllWeights

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 7000000
set_option backward.isDefEq.respectTransparency false

/-- The full parameter family, the parameter-independent zeroth iterate,
and all later iterates are constructed from the nonlinear existence theorem.
No existence of any perturbation iterate is assumed. -/
theorem perturbation_families_constructed
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
    : ∃ (sol : ℝ → BSDEFiniteEnergyData P F W c R)
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
          ε*f₁ ((w,r),(iter n ε).Y (realTimeClamp r) w,(iter n ε).Z (w,r)))) := by
  classical
  obtain ⟨base,hbt,hbB,_⟩ := nonlinear_bsde_driver_data_constructed P hT F hF hle hnull W A hW hA hclock
    c hc hcm hcT hct hcut hcc hco R hR hRT hFnat ξ hξ hξm f₀ hfm₀ hfp₀ hf₀ C₀
    (2*(1+R)*C₀^2+1) hC₀ (by linarith) hl₀
  have hs (ε : ℝ) : ∃ u : BSDEFiniteEnergyData P F W c R,
      (u.Y (realTimeClamp R) =ᵐ[P] ξ) ∧
      (∀ w r,r∈Icc 0 R → u.B (w,r)=
        -(f₀ ((w,r),u.Y (realTimeClamp r) w,u.Z (w,r))+
          ε*f₁ ((w,r),u.Y (realTimeClamp r) w,u.Z (w,r)))) := by
    let g := fun p => f₀ p+ε*f₁ p
    have hg : Measurable g := hfm₀.add (hfm₁.const_mul ε)
    have hgp : ∀ t : Icc (0:ℝ) R,
      @Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
        (fun p : Ω × (Iic t × (ℝ × ℝ)) => g ((p.1,p.2.1.val.val),p.2.2)) :=
      fun t => (hfp₀ t).add ((hfp₁ t).const_mul ε)
    have hg0 : MemLp (fun z => g (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))) :=
      hf₀.add (hf₁.const_smul ε)
    let C := C₀+|ε| * C₁
    obtain ⟨u,ht,hB,_⟩ := nonlinear_bsde_driver_data_constructed P hT F hF hle hnull W A hW hA hclock
      c hc hcm hcT hct hcut hcc hco R hR hRT hFnat ξ hξ hξm g hg hgp hg0 C
      (2*(1+R)*C^2+1) (add_nonneg hC₀ (mul_nonneg (abs_nonneg ε) hC₁)) (by linarith)
      (perturbed_generator_lipschitz f₀ f₁ C₀ C₁ ε |ε| hC₀ hC₁ le_rfl hl₀ hl₁)
    exact ⟨u,ht,hB⟩
  choose sol hst hsB using hs
  have hn (ε : ℝ) (prev : BSDEFiniteEnergyData P F W c R) :=
    perturbation_next_solution_constructed P hT F hF hle hnull W A hW hA hclock
      c hc hcm hcT hct hcut hcc hco R hR hRT hFnat ξ hξ hξm f₀ f₁ hfm₀ hfm₁ hfp₀ hfp₁ hf₀ hf₁
      C₀ C₁ ε hC₀ hC₁ hl₀ hl₁ prev
  choose next hnt hnB using hn
  let iter : ℕ → ℝ → BSDEFiniteEnergyData P F W c R :=
    fun n ε => Nat.rec base (fun _ prev => next ε prev) n
  refine ⟨sol,base,iter,fun _ => rfl,hst,?_,hsB,hbB,?_⟩
  · intro n ε
    cases n with
    | zero => exact hbt
    | succ n => exact hnt ε (iter n ε)
  · intro n ε
    exact hnB ε (iter n ε)

end Asakura.Chapter5
