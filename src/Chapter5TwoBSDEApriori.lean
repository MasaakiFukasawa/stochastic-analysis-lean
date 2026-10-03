import Chapter5BSDEFiniteEnergyData

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Apply the actual weighted Ito estimate to the difference of two
solutions. The discrepancy is the manuscript's delta_2 f; its L²
membership and the required difference bound are derived from f¹. -/
theorem two_bsde_apriori_constructed
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
    (u v : BSDEFiniteEnergyData P F W c R)
    (f : (Ω × ℝ) × (ℝ × ℝ) → ℝ) (hfm : Measurable f)
    (hf0 : MemLp (fun z => f (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (C β ell mu2 : ℝ) (hC : 0≤C) (hell : C<ell) (hmu2 : 0<mu2) (hβ : C*(2+ell)+mu2≤β)
    (hl : ∀ z y₁ z₁ y₂ z₂,|f (z,y₁,z₁)-f (z,y₂,z₂)|≤C*(|y₁-y₂|+|z₁-z₂|))
    (hBu : ∀ w r,r∈Icc 0 R → u.B (w,r)= -f ((w,r),u.Y (realTimeClamp r) w,u.Z (w,r))) :
    let D := fun z => f (z,v.Y (realTimeClamp z.2) z.1,v.Z z)+v.B z
    let K := (∫ w,Real.exp (β*R)*(u.Y (realTimeClamp R) w-v.Y (realTimeClamp R) w)^2 ∂P)+
      (∫ w,(∫ r in 0..R,Real.exp (β*r)*D (w,r)^2) ∂P)/mu2
    (∀ t∈Icc 0 R,(∫ w,Real.exp (β*t)*(u.Y (realTimeClamp t) w-v.Y (realTimeClamp t) w)^2 ∂P)≤K) ∧
      (∫ w,(∫ r in 0..R,Real.exp (β*r)*(u.Y (realTimeClamp r) w-v.Y (realTimeClamp r) w)^2) ∂P)≤R*K ∧
      (∫ w,(∫ r in 0..R,Real.exp (β*r)*(u.Z (w,r)-v.Z (w,r))^2) ∂P)≤ell/(ell-C)*K := by
  dsimp only
  let d := u.sub P F hF hle W c (fun j => (hc j).le) R v
  let D := fun z => f (z,v.Y (realTimeClamp z.2) z.1,v.Z z)+v.B z
  have hDm : Measurable D := (hfm.comp (measurable_id.prodMk (v.measurableY.prodMk v.measurableZ))).add v.measurableB
  have hfv := generator_memLp (P.prod (volume.restrict (Ioc 0 R))) f hfm
    (fun z => v.Y (realTimeClamp z.2) z.1) v.Z v.measurableY v.measurableZ v.energyY v.energyZ hf0 C hC
    (fun z y z' => by simpa only [sub_zero] using hl z y z' 0 0)
  have hDL : MemLp D 2 (P.prod (volume.restrict (Ioc 0 R))) := hfv.add v.energyB
  have hb w r (hr : r∈Icc 0 R) : |d.B (w,r)|≤C*(|d.Y (realTimeClamp r) w|+|d.Z (w,r)|)+|D (w,r)| := by
    change |u.B (w,r)-v.B (w,r)|≤C*(|u.Y (realTimeClamp r) w-v.Y (realTimeClamp r) w|+|u.Z (w,r)-v.Z (w,r)|)+|D (w,r)|
    rw [hBu w r hr]
    have hh := bsde_difference_generator_bound (fun y z => f ((w,r),y,z)) (fun _ _ => -v.B (w,r))
      (u.Y (realTimeClamp r) w) (u.Z (w,r)) (v.Y (realTimeClamp r) w) (v.Z (w,r)) C
      (hl (w,r) _ _ _ _)
    have he : -f ((w,r),u.Y (realTimeClamp r) w,u.Z (w,r))-v.B (w,r)=
        -(f ((w,r),u.Y (realTimeClamp r) w,u.Z (w,r))+v.B (w,r)) := by ring
    rw [he,abs_neg]
    simpa only [D,sub_neg_eq_add] using hh
  exact bsde_apriori_constructed P hT F hF hle hnull W A d.Y d.V d.M hW hA d.decomposition
    c hc hcm hcT hct hcut hcc hclock d.Z d.B d.measurableZ d.measurableB d.progressiveZ d.squareZ d.integrableB
    d.drift d.integral R hR hRT β C ell mu2 hC hell hmu2 hβ d.terminal d.energyZ d.energyB
    d.measurableY d.energyY D hDm hDL hb

end Asakura.Chapter5
