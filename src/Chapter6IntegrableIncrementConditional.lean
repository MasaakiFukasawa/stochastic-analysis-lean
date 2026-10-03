import Chapter4FinitePathLift
import Chapter6IntegrableLocalConditional

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- A process dominated by a square-integrable random variable whose increments are represented by a constructed
local martingale has the conditional martingale identity. -/
theorem integrable_local_increment_conditional
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X N : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (ha : ∀ t,t<⊤ → Measurable[F t] (X t))
    (R : ClosedTime T) (hR : R<⊤) (K : Ω → ℝ) (hK : Integrable K P)
    (hb : ∀ᵐ w ∂P,∀ t,t≤R → |X t w|≤K w)
    (he : ∀ᵐ w ∂P,∀ t,t≤R → X t w=X ⊥ w+N t w)
    (s : ClosedTime T) (hs : s≤R) :
    P[X R | F s]=ᵐ[P] X s := by
  have hnB : ∀ᵐ w ∂P,∀ t,‖N (min R t) w‖≤2*K w := by
    filter_upwards [he,hb] with w hw hbw
    intro t
    have hn : N (min R t) w=X (min R t) w-X ⊥ w := by linarith [hw (min R t) (min_le_left R t)]
    rw [hn,Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hbw _ (min_le_left R t),hbw ⊥ bot_le])
  have hmart := integrable_local_conditional P F hle N hN R hR (fun w => 2*K w) (hK.const_mul 2)
    (hnB.mono (fun w hw t ht => by simpa only [min_eq_right ht] using hw t)) s hs
  have hNi t (ht : t≤R) : Integrable (N t) P := by
    apply (hK.const_mul 2).mono' (((hN.adapted P F t (ht.trans_lt hR)).mono (hle t) le_rfl).aestronglyMeasurable)
    filter_upwards [hnB] with w hw
    simpa only [min_eq_right ht] using hw t
  have hiR := hNi R le_rfl
  have his := hNi s hs
  have hsi : Integrable (X s) P :=
    hK.mono' (((ha s (hs.trans_lt hR)).mono (hle s) le_rfl).aestronglyMeasurable)
      (hb.mono (fun w hw => by simpa only [Real.norm_eq_abs] using hw s hs))
  have hrep : X R=ᵐ[P] fun w => X s w+(N R w-N s w) := by
    filter_upwards [he] with w hw
    linarith [hw R le_rfl,hw s hs]
  have hadd := condExp_add hsi (hiR.sub his) (F s)
  have hsub := condExp_sub hiR his (F s)
  have hfix := condExp_of_stronglyMeasurable (hle s) (ha s (hs.trans_lt hR)).stronglyMeasurable hsi
  have hNs := condExp_of_stronglyMeasurable (hle s) (hN.adapted P F s (hs.trans_lt hR)).stronglyMeasurable his
  simp only [Pi.add_def,Pi.sub_def] at hadd hsub
  apply (condExp_congr_ae hrep).trans
  filter_upwards [hadd,hsub,hmart] with w h1 h2 h3
  rw [h1,h2]
  simp only [hfix,hNs,h3,sub_self,add_zero]

end Asakura.Chapter6
