import Chapter4DriftNoiseMoment
import Chapter4PrefixMoment
import Chapter3ContinuousItoEnergy
import Chapter3LocalEnergyMaximal
import Chapter4ClockVariationIntegral

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The scalar Picard difference estimate for actual drift and Ito integrals.
Coefficient integrability, supremum moments, and the Volterra right-hand side
are all derived from the manuscript Lipschitz and L2 path hypotheses. -/
theorem picard_integral_difference_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (W C H Z : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hC : LocalCovarianceWitness P F W W C)
    (hCm : ∀ ω, MonotoneOn (fun t => C t ω) (Iio ⊤))
    (hCc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => C s ω) t)
    (hclock : ∀ ω (r : ℝ), 0 ≤ r → (r:EReal) < T → C (realTimeClamp r) ω = r)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (hZ : LocalMProcessWitness P F Z)
    (hZI : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) Z)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (L : ℝ) (hL : 0 ≤ L) (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hLip : ∀ x y, (μ x-μ y)^2+(σ x-σ y)^2 ≤ L*(x-y)^2)
    (Y₁ Y₂ : Ω → C(Icc (0:ℝ) d,ℝ))
    (hm₁ : Measurable Y₁) (hm₂ : Measurable Y₂)
    (hi₁ : MemLp Y₁ 2 P) (hi₂ : MemLp Y₂ 2 P)
    (hH : ∀ ω r, r ∈ Icc 0 d → H (realTimeClamp r) ω =
      σ (Y₁ ω (projIcc 0 d hd r))-σ (Y₂ ω (projIcc 0 d hd r)))
    (D : Ω → C(Icc (0:ℝ) d,ℝ)) (hDm : AEStronglyMeasurable D P)
    (hD : ∀ᵐ ω ∂P, ∀ t, D ω t = ∫ r in 0..t.val,
      (μ (Y₁ ω (projIcc 0 d hd r))-μ (Y₂ ω (projIcc 0 d hd r)))) :
    ∃ hc : ∀ ω, Continuous (fun t => Z (min (realTimeClamp d) t) ω),
      MemLp (fun ω => D ω+finiteRealPath Z d hc ω) 2 P ∧
      (∫ ω, ‖D ω+finiteRealPath Z d hc ω‖^2 ∂P) ≤
        ((2*d+8)*L)*(∫ r in 0..d, (∫ ω, ‖prefixPath hd (Y₁ ω-Y₂ ω) r‖^2 ∂P)) := by
  let ν := P.prod (volume.restrict (Ioc (0:ℝ) d))
  let U := fun z : Ω × ℝ => μ (Y₁ z.1 (projIcc 0 d hd z.2))-μ (Y₂ z.1 (projIcc 0 d hd z.2))
  let K := fun z : Ω × ℝ => σ (Y₁ z.1 (projIcc 0 d hd z.2))-σ (Y₂ z.1 (projIcc 0 d hd z.2))
  let V := fun z : Ω × ℝ => Y₁ z.1 (projIcc 0 d hd z.2)-Y₂ z.1 (projIcc 0 d hd z.2)
  obtain ⟨hiV,hiU,hiK,hb⟩ := coefficient_difference_energy P d L hd hL μ σ hμ hσ hLip
    Y₁ Y₂ hm₁ hm₂ hi₁ hi₂
  have hgood : ∀ᵐ z ∂ν, z.2 ∈ Ioc (0:ℝ) d := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).2
    exact .of_forall (fun _ => ae_restrict_mem measurableSet_Ioc)
  have heH : (fun z : Ω × ℝ => H (realTimeClamp z.2) z.1) =ᵐ[ν] K := by
    filter_upwards [hgood] with z hz
    exact hH z.1 z.2 ⟨hz.1.le,hz.2⟩
  have hiH := (memLp_congr_ae heH).2 hiK
  have hU : Measurable U :=
    (hμ.measurable.comp (clamped_path_evaluation_measurable d hd Y₁ hm₁)).sub
      (hμ.measurable.comp (clamped_path_evaluation_measurable d hd Y₂ hm₂))
  obtain ⟨hc,hi,hbZ⟩ := drift_noise_path_moment P hT F hF hle hnull W C H Z
    hW hC hCm hCc hclock hHm hHc hZ hZI d hd hdT hiH U hU hiU D hDm hD
  have heE : (∫ z : Ω × ℝ, H (realTimeClamp z.2) z.1^2 ∂ν) = ∫ z, K z^2 ∂ν :=
    integral_congr_ae (heH.mono (fun _ h => congrArg (fun x : ℝ => x^2) h))
  change _ ≤ 2*d*(∫ z, U z^2 ∂ν)+8*(∫ z, H (realTimeClamp z.2) z.1^2 ∂ν) at hbZ
  rw [heE] at hbZ
  have hiU2 := (memLp_two_iff_integrable_sq hiU.aestronglyMeasurable).1 hiU
  have hiK2 := (memLp_two_iff_integrable_sq hiK.aestronglyMeasurable).1 hiK
  change (∫ z, (U z^2+K z^2) ∂ν) ≤ L*∫ z, V z^2 ∂ν at hb
  rw [integral_add hiU2 hiK2] at hb
  have hp := time_energy_le_prefix_moment P hd (fun ω => Y₁ ω-Y₂ ω)
    (hm₁.sub hm₂) (hi₁.sub hi₂)
  change (∫ z, V z^2 ∂ν) ≤ _ at hp
  have hUpos : 0 ≤ ∫ z, U z^2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
  have hKpos : 0 ≤ ∫ z, K z^2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨hc,hi,?_⟩
  calc
    _ ≤ 2*d*(∫ z, U z^2 ∂ν)+8*(∫ z, K z^2 ∂ν) := hbZ
    _ ≤ (2*d+8)*((∫ z, U z^2 ∂ν)+(∫ z, K z^2 ∂ν)) := by nlinarith
    _ ≤ (2*d+8)*(L*∫ z, V z^2 ∂ν) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hp (by positivity)

/-- Apply the difference estimate to two separately constructed Picard Ito
integrals. Their difference characterization is proved by Ito linearity. -/
theorem sde_picard_difference_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (W C Y₁ Y₂ Z₁ Z₂ : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hC : LocalCovarianceWitness P F W W C)
    (hCm : ∀ ω, MonotoneOn (fun t => C t ω) (Iio ⊤))
    (hCc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => C s ω) t)
    (hclock : ∀ ω (r : ℝ), 0 ≤ r → (r:EReal) < T → C (realTimeClamp r) ω = r)
    (hY₁m : ∀ t, t < ⊤ → Measurable[F t] (Y₁ t))
    (hY₂m : ∀ t, t < ⊤ → Measurable[F t] (Y₂ t))
    (hY₁c : ∀ ω t, t < ⊤ → ContinuousAt (fun s => Y₁ s ω) t)
    (hY₂c : ∀ ω t, t < ⊤ → ContinuousAt (fun s => Y₂ s ω) t)
    (L : ℝ) (hL : 0 ≤ L) (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hLip : ∀ x y, (μ x-μ y)^2+(σ x-σ y)^2 ≤ L*(x-y)^2)
    (hZ₁ : LocalMProcessWitness P F Z₁) (hZ₂ : LocalMProcessWitness P F Z₂)
    (hZI₁ : ItoCovarianceFormula P F W (fun z => σ (Y₁ (realTimeClamp z.2) z.1)) Z₁)
    (hZI₂ : ItoCovarianceFormula P F W (fun z => σ (Y₂ (realTimeClamp z.2) z.1)) Z₂)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (y₁ y₂ : Ω → C(Icc (0:ℝ) d,ℝ))
    (hm₁ : Measurable y₁) (hm₂ : Measurable y₂)
    (hi₁ : MemLp y₁ 2 P) (hi₂ : MemLp y₂ 2 P)
    (he₁ : ∀ ω r, r ∈ Icc 0 d → Y₁ (realTimeClamp r) ω = y₁ ω (projIcc 0 d hd r))
    (he₂ : ∀ ω r, r ∈ Icc 0 d → Y₂ (realTimeClamp r) ω = y₂ ω (projIcc 0 d hd r))
    (D : Ω → C(Icc (0:ℝ) d,ℝ)) (hDm : AEStronglyMeasurable D P)
    (hD : ∀ᵐ ω ∂P, ∀ t, D ω t = ∫ r in 0..t.val,
      (μ (y₁ ω (projIcc 0 d hd r))-μ (y₂ ω (projIcc 0 d hd r)))) :
    ∃ hc : ∀ ω, Continuous (fun t => Z₁ (min (realTimeClamp d) t) ω-Z₂ (min (realTimeClamp d) t) ω),
      MemLp (fun ω => D ω+finiteRealPath (fun t ω => Z₁ t ω-Z₂ t ω) d hc ω) 2 P ∧
      (∫ ω, ‖D ω+finiteRealPath (fun t ω => Z₁ t ω-Z₂ t ω) d hc ω‖^2 ∂P) ≤
        ((2*d+8)*L)*(∫ r in 0..d, (∫ ω, ‖prefixPath hd (y₁ ω-y₂ ω) r‖^2 ∂P)) := by
  let H := fun t ω => σ (Y₁ t ω)-σ (Y₂ t ω)
  let Z := fun t ω => Z₁ t ω-Z₂ t ω
  have hZ : LocalMProcessWitness P F Z := by
    simpa only [neg_one_mul,neg_add_eq_sub] using
      (hZ₂.smul P F (-1)).add P F hF hle hZ₁
  have hZI : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) Z := by
    simpa only [neg_one_mul,neg_add_eq_sub] using
      hZI₂.add_smul P F hF hle W Z₂ Z₁ _ _ hZI₁ (-1)
  have hHm t ht : Measurable[F t] (H t) :=
    (hσ.measurable.comp (hY₁m t ht)).sub (hσ.measurable.comp (hY₂m t ht))
  have hHc ω t ht : ContinuousAt (fun s => H s ω) t :=
    (hσ.continuousAt.comp (hY₁c ω t ht)).sub (hσ.continuousAt.comp (hY₂c ω t ht))
  exact picard_integral_difference_bound P hT F hF hle hnull W C H Z
    hW hC hCm hCc hclock hHm hHc hZ hZI d hd hdT L hL μ σ hμ hσ hLip
    y₁ y₂ hm₁ hm₂ hi₁ hi₂
    (fun ω r hr => by dsimp [H]; rw [he₁ ω r hr,he₂ ω r hr]) D hDm hD

end Asakura.Chapter4
