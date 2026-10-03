import Chapter11AffinePDECompactStop
import Chapter11BarrierSpatialLimit
import Chapter11BoundedStoppedExpectation

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

/-- Remove the compact spatial stops in the local C1,2 uniqueness proof.
 All stochastic representations used below are constructed by Ito's formula. -/
theorem affine_barrier_preterminal_expectation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (y a σ a0 R U : ℝ) (hy : y<0) (ha0 : a0<0) (hR : 0≤R) (hRU : R<U)
    (v : ℝ → ℝ → ℝ) (vt : ℝ × ℝ → ℝ)
    (hv : ∀ t∈Ioo a0 U,ContDiffOn ℝ 2 (v t) (Iio 0))
    (hvt : ∀ t∈Ioo a0 U,∀ x<0,HasDerivAt (fun s => v s x) (vt (t,x)) t)
    (hvc : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (Ioo a0 U ×ˢ Iio 0))
    (hvtc : ContinuousOn vt (Ioo a0 U ×ˢ Iio 0))
    (hdxc : ContinuousOn (fun z : ℝ × ℝ => deriv (v z.1) z.2) (Ioo a0 U ×ˢ Iio 0))
    (hxxc : ContinuousOn (fun z : ℝ × ℝ => deriv (deriv (v z.1)) z.2) (Ioo a0 U ×ˢ Iio 0))
    (hpde : ∀ t∈Icc 0 R,∀ z<0,vt (t,z)+deriv (v t) z*a+deriv (deriv (v t)) z*σ^2/2=0)
    (hboundary : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (Icc 0 R ×ˢ Iic 0))
    (K : ℝ) (hbound : ∀ t∈Icc 0 R,∀ z≤0,|v t z|≤K) :
    let X := fun t w => y+a*B.C 0 0 t w+σ*B.W 0 t w
    let Y := fun w =>
      let ρ := min (upperBarrierHit (fun t => X t w)) (realTimeClamp R)
      v (halfTimeReal ρ : ℝ) (X ρ w)
    Integrable Y P ∧ (∫ w,Y w ∂P)=v 0 y := by
  dsimp only
  let X := fun t w => y+a*B.C 0 0 t w+σ*B.W 0 t w
  obtain ⟨hX,_,_,_,hinit⟩ := affine_brownian_decomposition P B (fun _ => y) measurable_const a σ
  obtain ⟨k,hk⟩ := eventually_atTop.mp (eventually_inside_barrier_compacts y hy)
  let j := fun n : ℕ => n+k
  have hin n : -(j n:ℝ)<y ∧ y< -(1/((j n:ℝ)+1)) := hk _ (Nat.le_add_left _ _)
  let lo := fun n => -(j n:ℝ)
  let up := fun n => -(1/((j n:ℝ)+1))
  have hup n : up n<0 := neg_neg_of_pos (by positivity)
  have hu n : up n<up n/2 := by linarith [hup n]
  have hsub n : Ioo (lo n-1) (up n/2) ⊆ Iio (0:ℝ) := fun x hx =>
    hx.2.trans (by linarith [hup n])
  have hrect n : Ioo a0 U ×ˢ Ioo (lo n-1) (up n/2) ⊆ Ioo a0 U ×ˢ Iio (0:ℝ) :=
    fun z hz => ⟨hz.1,hsub n hz.2⟩
  have hex n := affine_pde_compact_stop P B y a σ a0 R U (lo n-1) (lo n) (up n) (up n/2)
    ha0 hR hRU (by linarith) (hin n).1 (hin n).2 (hu n) v vt
    (fun t ht => (hv t ht).mono (hsub n))
    (fun t ht x hx => hvt t ht x (hsub n hx))
    (hvc.mono (hrect n)) (hvtc.mono (hrect n)) (hdxc.mono (hrect n)) (hxxc.mono (hrect n))
    (fun t ht z hz => hpde t ht z (hz.2.trans_lt (hup n))) K
    (fun t ht z hz => hbound t ht z (hz.2.trans (hup n).le))
  choose τ N hτ hN he using hex
  let ρ := fun n w => min (intervalExit (fun t => X t w) (lo n) (up n)) (realTimeClamp R)
  let Z := fun n w => v (halfTimeReal (ρ n w) : ℝ) (X (ρ n w) w)
  have he' n : Z n=ᵐ[P] fun w => v 0 y+N n (realTimeClamp R) w := by
    filter_upwards [he n] with w hw
    have hh := hw R ⟨hR,le_rfl⟩
    rw [min_eq_left (τ n w).property.2] at hh
    have hq : realTimeClamp (τ n w).val=ρ n w := hτ n w
    change v (halfTimeReal (ρ n w) : ℝ) (X (ρ n w) w)=v 0 y+N n (realTimeClamp R) w
    rw [←hq]
    simpa only [changed_time_real _ (τ n w).property.1] using hh
  have hb n : ∀ᵐ w ∂P,|Z n w|≤K := by
    filter_upwards [hinit] with w hi
    have hi' : X ⊥ w=y := hi
    have hb := before_interval_exit_bounds (fun t => X t w) (hX.continuous w) (lo n) (up n)
      (by simpa only [hi'] using hin n) (τ n w).val (τ n w).property.1
      (by rw [hτ n w];exact min_le_left _ _)
    have hq : realTimeClamp (τ n w).val=ρ n w := hτ n w
    change |v (halfTimeReal (ρ n w) : ℝ) (X (ρ n w) w)|≤K
    rw [←hq,changed_time_real _ (τ n w).property.1]
    exact hbound _ (τ n w).property _ (hb.2.trans (hup n).le)
  apply bounded_stopped_expectation_limit P B.F B.le N hN (realTimeClamp R) Z _ (v 0 y) K he' hb
  filter_upwards [hinit] with w hi
  have hi' : X ⊥ w=y := hi
  have hl := barrier_candidate_spatial_limit (fun t => X t w) (hX.continuous w)
    (by rw [hi'];exact hy) R hR (fun z => v z.1 z.2) hboundary
  exact hl.comp (tendsto_add_atTop_nat k)

end Asakura.Chapter11
