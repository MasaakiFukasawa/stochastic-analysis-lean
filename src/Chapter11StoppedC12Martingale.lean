import Chapter4FinitePathLift
import Chapter11C12CommonRepresentation
import Chapter2SquareIntegrableStop

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- A bounded stopped PDE solution is an M2 martingale. The generator
 vanishes only before the exit, not on the arbitrary extension outside. -/
theorem bounded_stopped_c12_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (X N : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (g : ℝ → ℝ → ℝ) (G : Ω → ℝ → ℝ)
    (τ : Ω → Icc (0:ℝ) R)
    (hτ : ∀ t,MeasurableSet[F t] {w | realTimeClamp (τ w).val≤t})
    (he : ∀ᵐ w ∂P,∀ r∈Icc 0 R,g r (X (realTimeClamp r) w)=
      g 0 (X ⊥ w)+N (realTimeClamp r) w+∫ s in 0..r,G w s)
    (hG : ∀ᵐ w ∂P,∀ r∈Icc 0 (τ w).val,G w r=0)
    (K : ℝ) (hbound : ∀ᵐ w ∂P,∀ r∈Icc 0 (τ w).val,|g r (X (realTimeClamp r) w)|≤K) :
    ContinuousM2Witness P F (fun t w => N (min (realTimeClamp (τ w).val) t) w) ∧
      (∀ᵐ w ∂P,∀ r∈Icc 0 R,
        g (min (τ w).val r) (X (realTimeClamp (min (τ w).val r)) w)=
          g 0 (X ⊥ w)+N (min (realTimeClamp (τ w).val) (realTimeClamp r)) w) := by
  have htau w : realTimeClamp (T:=T) (τ w).val<⊤ :=
    real_time_below _ (τ w).property.1 ((EReal.coe_le_coe (τ w).property.2).trans_lt hRT)
  have hz : realTimeClamp (T:=T) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T:=T) 0:EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=T) 0 le_rfl ((EReal.coe_le_coe hR).trans hRT.le)
  have hrep : ∀ᵐ w ∂P,∀ r∈Icc 0 (τ w).val,g r (X (realTimeClamp r) w)=g 0 (X ⊥ w)+N (realTimeClamp r) w := by
    filter_upwards [he,hG] with w hw hg
    intro r hr
    have h := hw r ⟨hr.1,hr.2.trans (τ w).property.2⟩
    have hi : (∫ s in 0..r,G w s)=0 := by
      calc
        _ = ∫ s in 0..r,(0:ℝ) := intervalIntegral.integral_congr (fun s hs =>
          hg s (Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using hs)))
        _ = 0 := intervalIntegral.integral_zero
    simpa only [hi,add_zero] using h
  have hb : ∀ᵐ w ∂P,∀ t,‖N (min (realTimeClamp (τ w).val) t) w‖≤2*K := by
    filter_upwards [hrep,hbound] with w hw hb
    intro t
    obtain ⟨r,hr,hrT,hrt⟩ := finite_closed_time_real (min (realTimeClamp (τ w).val) t)
      ((min_le_left _ _).trans_lt (htau w))
    have hrτ : r≤(τ w).val := by
      have hh : realTimeClamp (T:=T) r≤realTimeClamp (τ w).val := hrt ▸ min_le_left _ _
      change (realTimeClamp r:EReal)≤(realTimeClamp (τ w).val:EReal) at hh
      rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq _ (τ w).property.1
        ((EReal.coe_le_coe (τ w).property.2).trans hRT.le)] at hh
      exact EReal.coe_le_coe_iff.mp hh
    have heq := hw r ⟨hr,hrτ⟩
    have hb0 := hb 0 ⟨le_rfl,(τ w).property.1⟩
    rw [hz] at hb0
    rw [←hrt,Real.norm_eq_abs,show N (realTimeClamp r) w=g r (X (realTimeClamp r) w)-g 0 (X ⊥ w) by linarith]
    exact (abs_sub _ _).trans (by linarith [hb r ⟨hr,hrτ⟩])
  refine ⟨local_stop_is_m2_of_square_integrable_bound P F hF hle N hN
    (fun w => realTimeClamp (τ w).val) hτ htau (fun _ => 2*K) (memLp_const _) hb,?_⟩
  filter_upwards [hrep] with w hw
  intro r hr
  simpa only [real_time_clamp_mono.map_min] using hw (min (τ w).val r)
    ⟨le_min (τ w).property.1 hr.1,min_le_left _ _⟩

end Asakura.Chapter11
