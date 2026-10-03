import Chapter5BackwardHeatGradient
import Chapter5ObservationPrefix

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The derivative integrands of every preterminal extension coincide
with the common Gaussian gradient before that cutoff. -/
theorem observation_gradient_prefix
    {Ω : Type*} {T : EReal} [Fact (0≤T)] {d k : ℕ}
    (W : Fin d → ClosedTime T → Ω → ℝ) (index : Fin k → Fin d)
    (active : Fin k → Prop) [DecidablePred active] (τ : Fin k → ℝ)
    (b S : ℝ) (hb : 0≤b) (hbS : b≤S) (hbT : (b:EReal)<T)
    (hcurrent : ∀ i,active i → τ i=b)
    (ν : Measure (Fin k → ℝ)) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : Fin k → ℝ => z) ν)
    (f : (Fin k → ℝ) → ℝ) (D : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ≥0) (hD : ∀ x,‖D x‖≤C)
    (g : ((Fin k → ℝ) × ℝ) → ℝ) (hg : ContDiff ℝ 2 g)
    (he : ∀ p : (Fin k → ℝ) × ℝ,p.2≤b → g p=∫ z,f (p.1+Real.sqrt (S-p.2) • z) ∂ν)
    (w : Ω) (r : ℝ) (hr : r∈Ioc 0 b) (i : Fin k) :
    fderiv ℝ (fun x => g (spaceTimeCoordinates k x))
      (Fin.cons (finitePrefixTime (T := T) b hb (realTimeClamp r)).val
        (fun j => W (index j) (min (realTimeClamp (τ j)) (realTimeClamp r)) w) : Fin (k+1) → ℝ)
      (Pi.single i.succ 1)=
      ∫ y,D ((fun j => W (index j) (min (realTimeClamp (if active j then S else τ j)) (realTimeClamp r)) w)+
        Real.sqrt (S-(finitePrefixTime (T := T) S (hb.trans hbS) (realTimeClamp r)).val) • y) (Pi.single i 1) ∂ν := by
  have hrT : (r:EReal)<T := (EReal.coe_le_coe hr.2).trans_lt hbT
  have hcb : (finitePrefixTime (T := T) b hb (realTimeClamp r)).val=r := by
    rw [clipped_clock_time_density b hb r hr.1.le hrT,clipped_clock_density_integral b r hb hr.1.le,min_eq_right hr.2]
  have hcs : (finitePrefixTime (T := T) S (hb.trans hbS) (realTimeClamp r)).val=r := by
    rw [clipped_clock_time_density S (hb.trans hbS) r hr.1.le hrT,
      clipped_clock_density_integral S r (hb.trans hbS) hr.1.le,min_eq_right (hr.2.trans hbS)]
  rw [hcb,hcs]
  rw [backward_extension_coordinate_gradient ν hi f D hd hDc C hD g hg b S he
    (Fin.cons r (fun j => W (index j) (min (realTimeClamp (τ j)) (realTimeClamp r)) w))
    (by simpa using hr.2) i]
  simp only [Fin.cons_zero,Fin.cons_succ]
  rw [observation_prefix_consistency W index active τ b S r hr.2 hbS hcurrent w]

end Asakura.Chapter5
