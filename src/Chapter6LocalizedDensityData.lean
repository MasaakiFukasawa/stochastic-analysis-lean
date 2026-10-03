import Chapter6StoppedEntropyIdentity
import Chapter6DensityProbability
import Chapter2OneSidedStoppedCovariance
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Stop the actual density martingale. Novikov constructs the probability
measure; Girsanov constructs the Brownian driver and the entropy identity. -/
theorem localized_density_data {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (Z C : HalfClosedTime → Ω → ℝ) (hZ : LocalMProcessWitness P B.F Z)
    (hC : LocalCovarianceWitness P B.F Z Z C)
    (L : Fin d → HalfClosedTime → Ω → ℝ)
    (hL : ∀ j,LocalCovarianceWitness P B.F Z (B.W j) (L j))
    (H : Fin d → Ω × ℝ → ℝ)
    (R : ℝ) (hR : 0≤R)
    (hLe : ∀ j,∀ᵐ w ∂P,∀ r∈Icc 0 R,L j (realTimeClamp r) w=∫ s in 0..r,H j (w,s))
    (τ : Ω → HalfClosedTime) (hτ : ∀ t,MeasurableSet[B.F t] {w | τ w≤t})
    (hτR : ∀ w,τ w≤realTimeClamp R)
    (K : ℝ) (hK : ∀ᵐ w ∂P,|C (τ w) w|≤K) :
    let u := fun w => (finitePrefixTime R hR (τ w)).val
    let D := fun w => Real.exp (Z (τ w) w-C (τ w) w/2)
    Measurable D ∧ Integrable D P ∧ (∫ w,D w ∂P)=1 ∧
    ∃ (Q : Measure Ω) (hQp : IsProbabilityMeasure Q),
      Q=P.withDensity (fun w => ENNReal.ofReal (D w)) ∧
      (∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w) ∧
      Integrable (fun w => D w*Real.log (D w)) P ∧
      (∫ w,D w*Real.log (D w) ∂P)=(∫ w,C (τ w) w ∂Q)/2 ∧
      ∃ BQ : BrownianSystem Q d,BQ.F=B.F ∧
        ∀ᵐ w ∂Q,∀ j (r : ℝ),r∈Icc 0 R →
          BQ.W j (realTimeClamp r) w=B.W j (realTimeClamp r) w-∫ s in 0..min (u w) r,H j (w,s) := by
  let u := fun w => (finitePrefixTime R hR (τ w)).val
  let D := fun w => Real.exp (Z (τ w) w-C (τ w) w/2)
  have hT : (0:EReal)<⊤ := by simp
  have hτt w := (hτR w).trans_lt (changed_time_finite R hR)
  have hc := (hC.stopped_regular P B.F B.mono B.le hZ hZ τ hτ hτt).1 ⊤
  simp only [min_top_right] at hc
  have hEi := exponential_integrable_of_upper_bound P _ (hc.mono (B.le _) le_rfl) K 1 (by norm_num)
    (hK.mono (fun w hw => (le_abs_self _).trans hw))
  obtain ⟨hDi,hDa,hmean,_⟩ := novikov_written P hT B.F B.mono B.le B.null Z C hZ hC τ hτ hτt 1 (by norm_num) hEi
  simp only [min_top_right] at hmean
  have hi : Integrable D P := by simpa only [D,min_top_right] using hDi ⊤
  have hz := (open_process_stopped_regular B.F B.mono Z (hZ.adapted P B.F) (hZ.path P B.F) τ hτ hτt).1 ⊤
  simp only [min_top_right] at hz
  have hm : Measurable D := ((hz.mono (B.le _) le_rfl).sub ((hc.mono (B.le _) le_rfl).div_const 2)).exp
  let Q := P.withDensity (fun w => ENNReal.ofReal (D w))
  haveI hQp : IsProbabilityMeasure Q := mean_one_density_probability P D hi (ae_of_all _ fun _ => (Real.exp_pos _).le) hmean
  have hAE := fun p => positive_real_density_ae_iff P Q D hm (ae_of_all _ fun _ => Real.exp_pos _) rfl p
  have hE := stopped_exponential_entropy_identity P Q B.F B.mono B.le B.null Z C hZ hC τ hτ R hR hτR K hK hmean rfl
  have hZs := hZ.stopped P B.F B.mono B.le τ hτ
  choose A hA using fun j => local_covariance_witness_exists P B.F B.mono B.le B.null
    (fun t w => Z (min (τ w) t) w) (B.W j) hZs (B.martingale j)
  obtain ⟨BQ,hBQ,hBWe⟩ := girsanov_brownian_vector_driver P Q B Z C hZ hC τ hτ hτt hmean rfl A hA
  refine ⟨hm,hi,hmean,Q,hQp,rfl,hAE,hE.1,hE.2,BQ,hBQ,?_⟩
  apply (hAE _).mp
  filter_upwards [ae_all_iff.mpr hLe,ae_all_iff.mpr (fun j =>
    local_covariance_one_sided_stopping P B.F B.mono B.le B.null Z (B.W j) (L j) (A j)
      hZ (B.martingale j) (hL j) τ hτ (hA j))] with w hl ha
  intro j r hr
  have hu : realTimeClamp (u w)=τ w := by
    rw [show u w=(finitePrefixTime R hR (τ w)).val from rfl,finite_prefix_time_clamp R hR (le_top : (R:EReal)≤⊤),min_eq_right (hτR w)]
  have hum : u w∈Icc 0 R := (finitePrefixTime R hR (τ w)).property
  have hem : min (τ w) (realTimeClamp r)=realTimeClamp (min (u w) r) := by
    rw [←hu,real_time_clamp_mono.map_min]
  change BQ.W j (realTimeClamp r) w=B.W j (realTimeClamp r) w-∫ s in 0..min (u w) r,H j (w,s)
  rw [hBWe,ha j _ (changed_time_finite r hr.1),hem,
    hl j (min (u w) r) ⟨le_min hum.1 hr.1,(min_le_left _ _).trans hum.2⟩]

end Asakura.Chapter6
