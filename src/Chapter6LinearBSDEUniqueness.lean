import Chapter6LinearBSDEDriver
import Chapter5SolutionClassUniqueness

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem linear_bsde_solution_unique
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
    (φ α β : Ω × ℝ → ℝ) (hφ : Measurable φ) (hα : Measurable α) (hβ : Measurable β)
    (hφp : ∀ t : Icc (0:ℝ) R,@Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
      (fun p : Ω × Iic t => φ (p.1,p.2.val.val)))
    (hαp : ∀ t : Icc (0:ℝ) R,@Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
      (fun p : Ω × Iic t => α (p.1,p.2.val.val)))
    (hβp : ∀ t : Icc (0:ℝ) R,@Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
      (fun p : Ω × Iic t => β (p.1,p.2.val.val)))
    (K : ℝ) (hK : 0≤K) (hφb : ∀ z,|φ z|≤K) (hαb : ∀ z,|α z|≤K) (hβb : ∀ z,|β z|≤K)
    (u v : BSDEFiniteEnergyData P F W c R)
    (hup : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => u.Y (realTimeClamp z.2.val) z.1))
    (hvp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => v.Y (realTimeClamp z.2.val) z.1))
    (hut : u.Y (realTimeClamp R)=ᵐ[P] ξ) (hvt : v.Y (realTimeClamp R)=ᵐ[P] ξ)
    (huB : ∀ w r,r∈Icc 0 R → u.B (w,r)= -(φ (w,r)+α (w,r)*u.Y (realTimeClamp r) w+β (w,r)*u.Z (w,r)))
    (hvB : ∀ w r,r∈Icc 0 R → v.B (w,r)= -(φ (w,r)+α (w,r)*v.Y (realTimeClamp r) w+β (w,r)*v.Z (w,r))) :
    ((fun z : Ω × ℝ => u.Y (realTimeClamp z.2) z.1)=ᵐ[P.prod (volume.restrict (Ioc 0 R))]
      fun z => v.Y (realTimeClamp z.2) z.1) ∧ (u.Z=ᵐ[P.prod (volume.restrict (Ioc 0 R))] v.Z) := by
  have hfp : ∀ t : Icc (0:ℝ) R,@Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
      (fun p : Ω × (Iic t × (ℝ × ℝ)) => linearBSDEDriver φ α β ((p.1,p.2.1.val.val),p.2.2)) := by
    intro t
    letI : MeasurableSpace Ω := F (realTimeClamp t.val)
    have hm : Measurable (fun p : Ω × (Iic t × (ℝ × ℝ)) => (p.1,p.2.1)) :=
      measurable_fst.prodMk measurable_snd.fst
    exact (((hφp t).comp hm).add (((hαp t).comp hm).mul measurable_snd.snd.fst)).add
      (((hβp t).comp hm).mul measurable_snd.snd.snd)
  have hu := nonlinear_bsde_fixed_point_constructed P hT F hF hle hnull W A hW hA hclock
    c hc hcm hcT hct hcut hcc hco R hR hRT hFnat ξ hξ hξm
    (linearBSDEDriver φ α β) (linear_bsde_driver_measurable φ α β hφ hα hβ) hfp
    (linear_bsde_driver_zero P φ α β hφ K R hφb) K (2*(1+R)*K^2+1) hK (by linarith)
    (linear_bsde_lipschitz φ α β K hαb hβb)
  exact nonlinear_solution_class_uniqueness P F W c hco R (2*(1+R)*K^2+1) hR
    (by positivity) ξ (linearBSDEDriver φ α β) hu u v hup hvp hut hvt huB hvB

end Asakura.Chapter6
