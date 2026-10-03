import Chapter2ElementaryLocalCovariance
import Chapter2CovarianceLimit
import Chapter2LocalizedApproximation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

lemma truncation_error_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (G : Ω → ℝ) (hG : Measurable G)
    (E : ℕ → Ω → ℝ) (he : ∀ (n : ℕ) w,|G w|≤(n:ℝ)+1 → E n w=0)
    (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun n => P {w | ε≤E n w}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (finite_real_tail_probability P (fun w => |G w|) hG.norm) (fun _ => bot_le)
  intro n
  apply measure_mono
  intro w hw
  by_contra hn
  have hz := he n w (le_of_not_gt hn)
  exact (not_le_of_gt hε) (hz ▸ hw)

/-- The elementary covariance formula extends to an unbounded predictable
weight whenever its elementary integral is a local martingale. Truncation
errors vanish outside the coefficient tails; no moment of the test
martingale is assumed. -/
theorem unbounded_elementary_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (a b : ClosedTime T) (hab : a≤b)
    (G : Ω → ℝ) (hGa : Measurable[F a] G)
    (hZ : LocalMProcessWitness P F (fun t w => G w*(X (min b t) w-X (min a t) w)))
    (D : ClosedTime T → Ω → ℝ)
    (hD : LocalCovarianceWitness P F (fun t w => G w*(X (min b t) w-X (min a t) w)) Y D)
    (t : ClosedTime T) (ht : t<⊤) :
    D t=ᵐ[P] fun w => G w*(C (min b t) w-C (min a t) w) := by
  classical
  let Gn := fun (n : ℕ) w => if |G w|≤(n:ℝ)+1 then G w else 0
  let Zn := fun n t w => Gn n w*(X (min b t) w-X (min a t) w)
  let Z := fun t w => G w*(X (min b t) w-X (min a t) w)
  have hGn n : Measurable[F a] (Gn n) := by
    letI : MeasurableSpace Ω := F a
    exact hGa.ite (measurableSet_le hGa.norm measurable_const) measurable_const
  have hGni n : MemLp (Gn n) ∞ P := by
    apply memLp_top_of_bound ((hGn n).mono (hle _) le_rfl).aestronglyMeasurable ((n:ℝ)+1)
    exact ae_of_all _ fun w => by
      dsimp only [Gn]
      split_ifs with hw
      · simpa only [Real.norm_eq_abs] using hw
      · simp only [norm_zero];positivity
  have hZn n := elementary_integral_local_martingale P F hF hle X hX a b hab (Gn n) (hGn n) (hGni n)
  choose Dn hDn using fun n => local_covariance_witness_exists P F hF hle hnull (Zn n) Y (hZn n) hY
  have hDe n := elementary_local_integral_covariance P F hF hle hnull X Y C hX hY hC a b hab (Gn n) (hGn n) (hGni n) (Dn n) (hDn n)
  obtain ⟨B,hB⟩ := local_covariance_witness_exists P F hF hle hnull Y Y hY hY
  have hprob (ε : ℝ) (hε : 0<ε) :
      Tendsto (fun n => P {w | ε≤⨆ s,|Zn n (min t s) w-Z (min t s) w|}) atTop (𝓝 0) := by
    apply truncation_error_probability P G (hGa.mono (hle _) le_rfl) _ _ ε hε
    intro n w hw
    have he : ∀ s, Zn n s w=Z s w := by intro s;simp only [Zn,Z,Gn,ite_eq_left hw]
    simp only [he,sub_self,abs_zero,ciSup_const]
  have hleft : TendstoInMeasure P (fun n => Dn n t) atTop (D t) := by
    rw [tendstoInMeasure_iff_norm]
    simpa only [Real.norm_eq_abs] using
      covariance_probability_continuity P F hF hle hnull Zn Dn Z Y B D hZn hZ hY hDn hB hD t ht hprob
  let Q := fun n w => Gn n w*(C (min b t) w-C (min a t) w)
  let Qlim := fun w => G w*(C (min b t) w-C (min a t) w)
  have hright : TendstoInMeasure P Q atTop Qlim := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    apply truncation_error_probability P G (hGa.mono (hle _) le_rfl) _ _ ε hε
    intro n w hw
    simp only [Q,Qlim,Gn,ite_eq_left hw,sub_self,norm_zero]
  apply tendstoInMeasure_ae_unique hleft
  apply hright.congr_left
  intro n
  have he : Dn n t=ᵐ[P] Q n := (hDe n).mono fun w hw => hw t ht
  exact he.symm

end Asakura.Chapter4
