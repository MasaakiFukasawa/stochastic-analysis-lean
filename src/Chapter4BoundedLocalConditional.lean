import Chapter4FinitePathLift
import Chapter2SquareIntegrableStop

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- A bounded process whose increments are represented by a constructed
local martingale has the conditional martingale identity. -/
theorem bounded_local_increment_conditional
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X N : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (ha : ∀ t,t<⊤ → Measurable[F t] (X t))
    (R : ClosedTime T) (hR : R<⊤) (K : ℝ)
    (hb : ∀ᵐ w ∂P,∀ t,t≤R → |X t w|≤K)
    (he : ∀ᵐ w ∂P,∀ t,t≤R → X t w=X ⊥ w+N t w)
    (s : ClosedTime T) (hs : s≤R) :
    P[X R | F s]=ᵐ[P] X s := by
  have hnB : ∀ᵐ w ∂P,∀ t,‖N (min R t) w‖≤2*K := by
    filter_upwards [he,hb] with w hw hbw
    intro t
    have hn : N (min R t) w=X (min R t) w-X ⊥ w := by linarith [hw (min R t) (min_le_left R t)]
    rw [hn,Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hbw _ (min_le_left R t),hbw ⊥ bot_le])
  have hM := local_stop_is_m2_of_square_integrable_bound P F hF hle N hN (fun _ => R)
    (fun t => by by_cases h : R≤t <;> simp [h]) (fun _ => hR) (fun _ => 2*K) (memLp_const _) hnB
  have hiR : Integrable (N R) P := by simpa only [min_self] using (hM.moment R).integrable (by norm_num)
  have his : Integrable (N s) P := by simpa only [min_eq_right hs] using (hM.moment s).integrable (by norm_num)
  have hsi : Integrable (X s) P := Integrable.of_bound
    ((ha s (hs.trans_lt hR)).mono (hle s) le_rfl).aestronglyMeasurable K
    (hb.mono fun w hw => hw s hs)
  have hrep : X R=ᵐ[P] fun w => X s w+(N R w-N s w) := by
    filter_upwards [he] with w hw
    linarith [hw R le_rfl,hw s hs]
  have hmart := hM.martingale s R hs
  simp only [min_self,min_eq_right hs] at hmart
  have hadd := condExp_add hsi (hiR.sub his) (F s)
  have hsub := condExp_sub hiR his (F s)
  have hfix := condExp_of_stronglyMeasurable (hle s) (ha s (hs.trans_lt hR)).stronglyMeasurable hsi
  have hNs := condExp_of_stronglyMeasurable (hle s) (hN.adapted P F s (hs.trans_lt hR)).stronglyMeasurable his
  simp only [Pi.add_def,Pi.sub_def] at hadd hsub
  apply (condExp_congr_ae hrep).trans
  filter_upwards [hadd,hsub,hmart] with w h1 h2 h3
  rw [h1,h2]
  simp only [hfix,hNs,h3,sub_self,add_zero]

end Asakura.Chapter4
