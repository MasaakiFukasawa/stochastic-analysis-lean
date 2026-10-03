import Chapter5NonlinearBSDEDriverData
import Chapter5BSDEProgressiveY
import Chapter5WeightedProcess
import Chapter5PerturbedGenerator

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- Every perturbation iterate actually exists, by applying the proved
nonlinear existence theorem to f0 plus the previous iterate's frozen
f1 term. All measurability and energy hypotheses are derived. -/
theorem perturbation_next_solution_constructed
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
    (C₀ C₁ ε : ℝ) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁)
    (hl₀ : ∀ z y₁ z₁ y₂ z₂,|f₀ (z,y₁,z₁)-f₀ (z,y₂,z₂)|≤C₀*(|y₁-y₂|+|z₁-z₂|))
    (hl₁ : ∀ z y₁ z₁ y₂ z₂,|f₁ (z,y₁,z₁)-f₁ (z,y₂,z₂)|≤C₁*(|y₁-y₂|+|z₁-z₂|))
    (prev : BSDEFiniteEnergyData P F W c R) :
    ∃ next : BSDEFiniteEnergyData P F W c R,
      (next.Y (realTimeClamp R) =ᵐ[P] ξ) ∧
      (∀ w r,r∈Icc 0 R → next.B (w,r)=
        -(f₀ ((w,r),next.Y (realTimeClamp r) w,next.Z (w,r))+
          ε*f₁ ((w,r),prev.Y (realTimeClamp r) w,prev.Z (w,r)))) := by
  let G := fun z => f₁ (z,prev.Y (realTimeClamp z.2) z.1,prev.Z z)
  have hGm : Measurable G := hfm₁.comp (measurable_id.prodMk (prev.measurableY.prodMk prev.measurableZ))
  have hG2 := generator_memLp _ f₁ hfm₁ _ _ prev.measurableY prev.measurableZ prev.energyY prev.energyZ hf₁ C₁ hC₁
    (fun z y z' => by simpa only [sub_zero] using hl₁ z y z' 0 0)
  have hGp := generator_progressive_substitution R (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))
    (fun w r y z => f₁ ((w,r),y,z)) hfp₁ (fun z => prev.Y (realTimeClamp z.2) z.1) prev.Z (prev.progressiveY P F hF W c R hR hRT)
    (prev.outputZ P F W c hco R).progressive
  let g := fun p : (Ω × ℝ) × (ℝ × ℝ) => f₀ p+ε*G p.1
  have hgm : Measurable g := hfm₀.add ((hGm.comp measurable_fst).const_mul ε)
  have hg0 : MemLp (fun z => g (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))) := hf₀.add (hG2.const_smul ε)
  have hgp : ∀ t : Icc (0:ℝ) R,
      @Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
        (fun p : Ω × (Iic t × (ℝ × ℝ)) => g ((p.1,p.2.1.val.val),p.2.2)) := by
    intro t
    letI : MeasurableSpace Ω := F (realTimeClamp t.val)
    have hp := (measurable_progressive_iff _ _).mp hGp t
    exact (hfp₀ t).add ((hp.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).const_mul ε)
  obtain ⟨next,ht,hB,_⟩ := nonlinear_bsde_driver_data_constructed P hT F hF hle hnull W A hW hA hclock
    c hc hcm hcT hct hcut hcc hco R hR hRT hFnat ξ hξ hξm g hgm hgp hg0 C₀
    (2*(1+R)*C₀^2+1) hC₀ (by linarith) (frozen_perturbed_generator_lipschitz f₀ G C₀ ε hl₀)
  exact ⟨next,ht,hB⟩

end Asakura.Chapter5
