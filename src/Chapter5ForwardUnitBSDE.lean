import Chapter5UnitOpenFeynmanKac
import Chapter5TimeReversePDE

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The actual finite-horizon BSDE associated with a forward solution. -/
def ForwardUnitBSDE {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (X : ClosedTime T → Ω → ℝ)
    (R : ℝ) (hR : 0≤R) (u : ℝ × ℝ → ℝ) (b : ℝ → ℝ → ℝ) : Prop :=
  ∃ N : ClosedTime T → Ω → ℝ,
    LocalMProcessWitness P F N ∧
    ItoCovarianceFormula P F X
      (fun z => deriv (fun y => u (R-(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,y))
        (X (realTimeClamp z.2) z.1)) N ∧
    ∀ t∈Icc 0 R,(fun w => u (0,X (realTimeClamp R) w)) =ᵐ[P]
      fun w => u (R-t,X (realTimeClamp t) w)-
        (∫ r in t..R,b (u (R-r,X (realTimeClamp r) w))
          (deriv (fun y => u (R-r,y)) (X (realTimeClamp r) w)))+
        (N (realTimeClamp R) w-N (realTimeClamp t) w)

/-- Forward PDE -> time reversal -> open-neighborhood Feynman--Kac ->
actual Ito integral. No desired BSDE identity is an input. -/
theorem forward_unit_PDE_to_BSDE
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (u : ℝ × ℝ → ℝ) (O : Set (ℝ × ℝ)) (hO : IsOpen O)
    (hstrip : {p : ℝ × ℝ | 0≤p.1} ⊆ O) (hu : ContDiffOn ℝ 2 u O)
    (b : ℝ → ℝ → ℝ)
    (hpde : ∀ t x,0≤t → deriv (fun r => u (r,x)) t=
      deriv (fun y => deriv (fun z => u (t,z)) y) x/2+b (u (t,x)) (deriv (fun y => u (t,y)) x))
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → C (realTimeClamp r) w = r) : ForwardUnitBSDE P F X R hR u b := by
  let v := fun p : Fin 2 → ℝ => u (R-p 0,p 1)
  let U := {p : Fin 2 → ℝ | (R-p 0,p 1)∈O}
  obtain ⟨hU,hs,hv,ht,hp⟩ := time_reverse_forward_PDE u O hO hstrip hu b hpde R hR
  obtain ⟨N,hN,hNI,hEq⟩ := nonlinear_feynman_kac_unit_open P hT F hF hle hnull X C hX hC
    R hR hRT v U hU hs hv (fun _ => b) (fun x => u (0,x)) ht hp c hc hcm hcT hcc hclock
  have hx (r x : ℝ) (hr : r∈Icc 0 R) :
      fderiv ℝ v ![r,x] (Pi.single 1 1)=deriv (fun y => u (R-r,y)) x := by
    exact fin2_space_derivative v r x
      ((hv.contDiffAt (hU.mem_nhds (hs (by simpa using hr)))).differentiableAt (by norm_num))
  refine ⟨N,hN,?_,?_⟩
  · convert hNI using 1
    funext z
    exact (hx _ _ (finitePrefixTime (T := T) R hR (realTimeClamp z.2)).property).symm
  · intro t ht'
    filter_upwards [hEq t ht'] with w hw
    change u (0,X (realTimeClamp R) w)=u (R-t,X (realTimeClamp t) w)-_+_
    have hi : (∫ r in t..R,b (v ![r,X (realTimeClamp r) w])
        (fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 1 1)))=
        ∫ r in t..R,b (u (R-r,X (realTimeClamp r) w))
        (deriv (fun y => u (R-r,y)) (X (realTimeClamp r) w)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht'.2] at hr
      dsimp only
      rw [hx r _ ⟨ht'.1.trans hr.1,hr.2⟩]
      rfl
    rwa [hi] at hw

end Asakura.Chapter5
