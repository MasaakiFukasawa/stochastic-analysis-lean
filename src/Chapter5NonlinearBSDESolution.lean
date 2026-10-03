import Chapter5NonlinearBSDEFixedPoint
import Chapter5FixedPointIsSolution

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Actual nonlinear BSDE existence, from terminal representation through
weighted Ito estimates and the complete-space contraction. -/
theorem nonlinear_bsde_solution_constructed
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
    (f : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm : Measurable f)
    (hfp : ∀ t : Icc (0:ℝ) R,
      @Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
        (fun p : Ω × (Iic t × (ℝ × ℝ)) => f ((p.1,p.2.1.val.val),p.2.2)))
    (hf0 : MemLp (fun z => f (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C β : ℝ) (hC : 0≤C) (hb : 2*(1+R)*C^2<β)
    (hl : ∀ z y₁ z₁ y₂ z₂,|f (z,y₁,z₁)-f (z,y₂,z₂)|≤C*(|y₁-y₂|+|z₁-z₂|)) :
    ∃ u : BSDEFiniteEnergyData P F W c R,
      ∀ t∈Icc 0 R,u.Y (realTimeClamp t) =ᵐ[P]
        fun w => ξ w+(∫ r in t..R,f ((w,r),u.Y (realTimeClamp r) w,u.Z (w,r)))-
          (u.M (realTimeClamp R) w-u.M (realTimeClamp t) w) := by
  obtain ⟨x,hx,_⟩ := nonlinear_bsde_fixed_point_constructed P hT F hF hle hnull W A hW hA hclock
    c hc hcm hcT hct hcut hcc hco R hR hRT hFnat ξ hξ hξm f hfm hfp hf0 C β hC hb hl
  exact frozen_class_fixed_point_is_solution P F W c (fun j => (hc j).le) hcT hco R β hR hRT
    (by nlinarith [sq_nonneg C]) ξ f hfm hf0 C hC
    (fun z y z' => by simpa only [sub_zero] using hl z y z' 0 0) x hx

end Asakura.Chapter5
