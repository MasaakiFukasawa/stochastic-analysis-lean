import Chapter11AffineBarrierExpectation
import Chapter11BarrierCandidateTerminal
import Chapter11BoundedMeanLimit

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The second passage to the limit in the barrier uniqueness proof.
 The exceptional corner is removed by the actual Brownian Gaussian law. -/
theorem affine_barrier_terminal_expectation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (y a σ T : ℝ) (hy : y<0) (hσ : 0<σ) (hT : 0<T)
    (v : ℝ → ℝ → ℝ) (payoff : ℝ → ℝ)
    (hboundary : ∀ t∈Ico 0 T,v t 0=0)
    (hterminal : ∀ z,z<0 → v T z=payoff z)
    (hcont : ∀ z,z<0 → ContinuousWithinAt (fun q : ℝ × ℝ => v q.1 q.2)
      (Icc 0 T ×ˢ Iic 0) (T,z))
    (K : ℝ) (hbound : ∀ t∈Ico 0 T,∀ z≤0,|v t z|≤K)
    (hpre : ∀ R∈Ico 0 T,
      let X := fun t w => y+a*B.C 0 0 t w+σ*B.W 0 t w
      let Y := fun w => let ρ := min (upperBarrierHit (fun t => X t w)) (realTimeClamp R)
        v (halfTimeReal ρ : ℝ) (X ρ w)
      Integrable Y P ∧ (∫ w,Y w ∂P)=v 0 y) :
    let X := fun t w => y+a*B.C 0 0 t w+σ*B.W 0 t w
    let Y := fun w => if realTimeClamp T<upperBarrierHit (fun t => X t w)
      then payoff (X (realTimeClamp T) w) else 0
    Integrable Y P ∧ (∫ w,Y w ∂P)=v 0 y := by
  dsimp only
  let X := fun t w => y+a*B.C 0 0 t w+σ*B.W 0 t w
  let Z := fun R w => let ρ := min (upperBarrierHit (fun t => X t w)) (realTimeClamp R)
    v (halfTimeReal ρ : ℝ) (X ρ w)
  obtain ⟨hX,_,_,_,hinit⟩ := affine_brownian_decomposition P B (fun _ => y) measurable_const a σ
  have hclock w t (ht : 0≤t) : B.C 0 0 (realTimeClamp t) w=t :=
    B.diagonal_clock 0 w t ht
  have hne : ∀ᵐ w ∂P,X (realTimeClamp T) w≠0 := by
    have hh := brownian_log_terminal_no_atom P B y (a+σ^2/2) σ T hσ hT
    simpa only [barrierLogStock,changed_time_real T hT.le,add_sub_cancel_right,hclock _ T hT.le,X] using hh
  obtain ⟨q,hqm,hq,hqlim⟩ := exists_seq_strictMono_tendsto' hT
  have hqT n : q n∈Ico 0 T := ⟨(hq n).1.le,(hq n).2⟩
  apply bounded_fixed_mean_limit P (fun n => Z (q n)) _ (v 0 y) K
    (fun n => (hpre _ (hqT n)).1) (fun n => (hpre _ (hqT n)).2)
  · intro n
    filter_upwards [hinit] with w hi
    have hi' : X ⊥ w=y := hi
    let ρ := min (upperBarrierHit (fun t => X t w)) (realTimeClamp (q n))
    have hρt : ρ<⊤ := (min_le_right _ _).trans_lt (real_time_below _ (hqT n).1 (EReal.coe_lt_top _))
    obtain ⟨s,hs,_,hse⟩ := finite_closed_time_real ρ hρt
    have hsR : s≤q n := by
      have hh : realTimeClamp (T:=(⊤:EReal)) s≤realTimeClamp (q n) := hse ▸ min_le_right _ _
      change (realTimeClamp s:EReal)≤(realTimeClamp (q n):EReal) at hh
      rw [real_time_clamp_eq s hs le_top,real_time_clamp_eq _ (hqT n).1 le_top] at hh
      exact EReal.coe_le_coe_iff.mp hh
    have hb := before_upper_hit_nonpos (fun t => X t w) (hX.continuous w)
      (by rw [hi'];exact hy) s hs (by rw [hse];exact min_le_left _ _)
    change |v (halfTimeReal ρ : ℝ) (X ρ w)|≤K
    rw [←hse,changed_time_real s hs]
    exact hbound s ⟨hs,hsR.trans_lt (hqT n).2⟩ _ hb
  · filter_upwards [hinit,hne] with w hi hn
    have hi' : X ⊥ w=y := hi
    have hl := barrier_candidate_terminal_limit (fun t => X t w) (hX.continuous w)
      (by rw [hi'];exact hy) T hT hn v payoff hboundary hterminal hcont
    exact hl.comp (tendsto_nhdsWithin_iff.mpr ⟨hqlim,Eventually.of_forall fun n => (hq n).2⟩)

end Asakura.Chapter11
