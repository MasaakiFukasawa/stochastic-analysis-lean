import Chapter11BarrierValuation
import Chapter11TerminalEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- Stopping a preterminal gradient preserves progressiveness and its
pathwise square integrability. -/
theorem stopped_open_gradient_regularity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (R T : ℝ) (hR : 0≤R) (hRT : R<T)
    (v : (Fin 2 → ℝ) → ℝ) (hv : ContDiffOn ℝ 2 v {q | q 0<T})
    (τ : Ω → HalfClosedTime) (hτ : ∀ t,MeasurableSet[B.F t] {w | τ w≤t}) :
    let G := fun z : Ω × ℝ => (Ioc (⊥ : HalfClosedTime) (τ z.1)).indicator
      (fun _ => fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
        B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) (realTimeClamp z.2)
    (∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => G (z.1,z.2.val))) ∧
      (∀ d,0<d → ∀ w,IntervalIntegrable (fun r => (G (w,r))^2) volume 0 d) := by
  classical
  dsimp only
  obtain ⟨hm,hp,hi⟩ := open_price_gradient_regularity P B R T hR hRT v hv
  have hbot : ∀ t,MeasurableSet[B.F t] {w : Ω | (⊥ : HalfClosedTime)≤t} := by simp
  constructor
  · intro d hd
    exact stopping_interval_prefix_progressive B.F B.mono (fun _ => ⊥) τ hbot hτ d
      (fun z : Ω × ℝ => fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val, B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) (hp d hd)
  · intro d hd w
    let G := fun r => fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp r)).val,
      B.W 0 (realTimeClamp r) w] (Pi.single 1 1)
    have hs : MeasurableSet {r : ℝ | realTimeClamp (T:=(⊤:EReal)) r∈Ioc (⊥ : HalfClosedTime) (τ w)} :=
      real_time_clamp_continuous.measurable measurableSet_Ioc
    have heq : (fun r => ((Ioc (⊥ : HalfClosedTime) (τ w)).indicator (fun _ => G r) (realTimeClamp r))^2)=
        {r : ℝ | realTimeClamp (T:=(⊤:EReal)) r∈Ioc (⊥ : HalfClosedTime) (τ w)}.indicator (fun r => G r^2) := by
      funext r
      simp only [indicator_apply,mem_setOf_eq]
      split_ifs <;> simp
    change IntervalIntegrable (fun r => ((Ioc (⊥ : HalfClosedTime) (τ w)).indicator (fun _ => G r) (realTimeClamp r))^2) volume 0 d
    rw [heq]
    exact ⟨(hi d hd w).1.indicator hs,(hi d hd w).2.indicator hs⟩

/-- The isometry yields a uniform energy bound from a bounded actual
stopped price. No expected-energy assumption is made. -/
theorem stopped_price_energy_bound {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (G : Ω × ℝ → ℝ)
    (hp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => G (z.1,z.2.val)))
    (hi : ∀ d,0<d → ∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)^2) volume 0 d)
    (N : HalfClosedTime → Ω → ℝ) (hN : ContinuousM2Witness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) G N)
    (R a K : ℝ) (hR : 0≤R) (hK : 0≤K) (ha : |a|≤K)
    (hb : ∀ᵐ w ∂P,|a+N (realTimeClamp R) w|≤K) :
    Integrable (fun w => ∫ r in 0..R,G (w,r)^2) P ∧
      (∫ w,(∫ r in 0..R,G (w,r)^2) ∂P)≤(2*K)^2 := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (T:=(⊤:EReal)) (by simp)
  have hNl := continuous_m2_is_local P B.F B.mono B.le
    (fun n => realTimeClamp (c n)) hct.monotone hcut hcc N hN
  obtain ⟨he,heq,_⟩ := brownian_prefix_energy_of_price P B G hp hi N N hNl hNI hN R hR
    (fun t ht => Filter.EventuallyEq.rfl)
  refine ⟨he,?_⟩
  rw [heq]
  have hni : Integrable (fun w => (N (realTimeClamp R) w)^2) P :=
    (memLp_two_iff_integrable_sq (hN.moment _).aestronglyMeasurable).mp (hN.moment _)
  calc
    (∫ w,(N (realTimeClamp R) w)^2 ∂P)≤∫ _ : Ω,(2*K)^2 ∂P := by
      apply integral_mono_ae hni (integrable_const _)
      filter_upwards [hb] with w hw
      have hab : |N (realTimeClamp R) w|≤2*K := by
        calc
          |N (realTimeClamp R) w|=|(a+N (realTimeClamp R) w)-a| := by congr 1;ring
          _≤|a+N (realTimeClamp R) w|+|a| := abs_sub _ _
          _≤2*K := by linarith
      have hs := pow_le_pow_left₀ (abs_nonneg (N (realTimeClamp R) w)) hab 2
      simpa only [sq_abs] using hs
    _=(2*K)^2 := by simp

end Asakura.Chapter11
