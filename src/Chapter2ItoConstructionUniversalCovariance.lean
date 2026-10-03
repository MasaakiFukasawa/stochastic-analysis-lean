import Chapter2ItoApproximationLimit
import Chapter2LocalDensity
import Chapter2ItoEnergyAtTime
import Chapter2ItoCovarianceAtTime
import Chapter2StieltjesErrorRestriction
import Chapter2ProgressiveRestrictedEnergy
import Chapter2ProgressiveFiniteEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The existence construction of the Ito integral from the manuscript's
Hilbert-space density proof and M_loc completion. No Ito operator, integral
process, approximating sequence or convergence conclusion is assumed.
The increasing representative A is the quadratic variation of X. -/
theorem ito_integral_constructed_with_universal_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure) :
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → ℝ) (V : ℕ → ℕ → Ω → ℝ)
      (Z : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ)) (Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ)),
      (∀ n, StrictMonoOn (u n) (Iic (N n))) ∧
      (∀ n i, i ≤ N n → u n i ∈ Icc 0 (c n)) ∧
      (∀ n i, i < N n → Measurable[F (realTimeClamp (u n i))] (V n i) ∧ MemLp (V n i) ∞ P) ∧
      (∀ n ω t, Z n ω t = ∑ i ∈ Finset.range (N n), V n i ω*
        stepIncrement (realTimeClamp (u n i)) (realTimeClamp (u n (i+1))) (fun s => X s ω) t.val) ∧
      LocalMProcessWitness P F (fun t ω => extendOpenPath (Y ω) t) ∧
      Tendsto (fun n => ∫ ω, pathDistance (intervalTimeExhaustion (fun n => realTimeClamp (c n)) hct hcut hcc)
        (Z n ω) (Y ω) ∂P) atTop (𝓝 0) ∧
      (∀ j (ε : ℝ), 0 < ε → Tendsto (fun n => P {ω | ε ≤ ∫ r,
        ((∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r)-H (ω,r))^2
        ∂(intervalStieltjes 0 (c j) (hc j).le (fun r => A (realTimeClamp r) ω) (hAm j ω)
          (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0)) ∧
      ∀ (Y0 B0 C0 : ClosedTime T → Ω → ℝ),
        LocalMProcessWitness P F Y0 →
        LocalCovarianceWitness P F Y0 Y0 B0 →
        LocalCovarianceWitness P F X Y0 C0 →
        (∀ n ω, MonotoneOn (fun r => B0 (realTimeClamp r) ω) (Icc 0 (c n))) →
        (∀ n ω, ContinuousOn (fun r => B0 (realTimeClamp r) ω) (Icc 0 (c n))) →
      ∃ D : ClosedTime T → Ω → ℝ,
      LocalCovarianceWitness P F (fun t ω => extendOpenPath (Y ω) t) Y0 D ∧
      (∀ j d (hd : 0 ≤ d), d ≤ c j → ∃ ν : Ω → SignedMeasure ℝ,
        (∀ ω a b, 0 ≤ a → a ≤ b → ν ω (Ioc a b) =
          C0 (min (realTimeClamp b) (realTimeClamp d)) ω-C0 (min (realTimeClamp a) (realTimeClamp d)) ω) ∧
        D (realTimeClamp d) =ᵐ[P] fun ω => signedIntegralRaw (ν ω) (fun r => H (ω,r))) := by
  classical
  have hbelow j r (hr : r ∈ Icc 0 (c j)) : realTimeClamp (T := T) r < ⊤ :=
    (real_time_clamp_mono hr.2).trans_lt (hcut j)
  have hAdapt (t : ClosedTime T) (ht : t < ⊤) : Measurable[F t] (A t) := by
    have h := ((hX.adapted P F t ht).mul (hX.adapted P F t ht)).sub (hA.defect.adapted P F t ht)
    convert h using 1
    funext ω
    change A t ω = X t ω*X t ω-(X t ω*X t ω-A t ω)
    ring
  let Ar := fun ω r => if realTimeClamp (T := T) r < ⊤ then A (realTimeClamp r) ω else 0
  have hAr j ω r (hr : r ∈ Icc 0 (c j)) : Ar ω r = A (realTimeClamp r) ω := by
    simp only [Ar,if_pos (hbelow j r hr)]
  have hArm r : Measurable[m] (fun ω => Ar ω r) := by
    by_cases hr : realTimeClamp (T := T) r < ⊤
    · simpa only [Ar,if_pos hr] using (hAdapt _ hr).mono (hle _) le_rfl
    · simp only [Ar,if_neg hr]
      exact measurable_const
  have hArmono j ω : MonotoneOn (Ar ω) (Icc 0 (c j)) := by
    intro r hr s hs hrs
    rw [hAr j ω r hr,hAr j ω s hs]
    exact hAm j ω hr hs hrs
  have hArc j ω : ContinuousOn (Ar ω) (Icc 0 (c j)) :=
    (hAc j ω).congr (fun r hr => hAr j ω r hr)
  have hArad j (t : Icc (0:ℝ) (c j)) : Measurable[F (realTimeClamp t.val)] (fun ω => Ar ω t.val) := by
    have he : (fun ω => Ar ω t.val) = A (realTimeClamp t.val) := funext (fun ω => hAr j ω t.val t.property)
    rw [he]
    exact hAdapt _ (hbelow j t.val t.property)
  have hμ j ω :
      (intervalStieltjes 0 (c j) (hc j).le (Ar ω) (hArmono j ω)
        (fun r hr => (hArc j ω r hr).mono inter_subset_left)).measure =
      (intervalStieltjes 0 (c j) (hc j).le (fun r => A (realTimeClamp r) ω) (hAm j ω)
        (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure := by
    apply interval_stieltjes_measure_congr_add_const 0 (c j) (hc j).le
      (fun r => A (realTimeClamp r) ω) (Ar ω) (hAm j ω) (hArmono j ω)
      (fun r hr => (hAc j ω r hr).mono inter_subset_left)
      (fun r hr => (hArc j ω r hr).mono inter_subset_left) 0
    intro r hr
    simpa only [add_zero] using hAr j ω r hr
  have hHiar j : ∀ᵐ ω ∂P, Integrable (fun r => |H (ω,r)|^(2:ℝ))
      (intervalStieltjes 0 (c j) (hc j).le (Ar ω) (hArmono j ω)
        (fun r hr => (hArc j ω r hr).mono inter_subset_left)).measure := by
    simpa only [hμ,Real.rpow_two,sq_abs] using hi j
  obtain ⟨N,u,V,hu,hub,hVm,hint,hprob⟩ := local_step_density P c hc hcm.monotone Ar hArmono hArc hArm
    (fun r => F (realTimeClamp r)) (hF.comp real_time_clamp_mono) (fun r => hle _)
    (fun j r hr => hArad j ⟨r,hr⟩) (fun r => hnull (realTimeClamp r)) H hH 2 (by norm_num) hHiar
  simp only [hμ,Real.rpow_two,sq_abs] at hint hprob
  obtain ⟨Z,Y,hZ,hY,hlim⟩ := elementary_approximation_local_martingale_limit P hT F hF hle hnull X A hX hA
    c (fun n => (hc n).le) hcm hcT hct hcut hcc hAm hAc N u V hu hub
    (fun n i hi => (hVm n i hi).1) (fun n i hi => (hVm n i hi).2) (fun ω r => H (ω,r)) hint hprob
  refine ⟨N,u,V,Z,Y,hu,hub,hVm,hZ,hY,hlim,hprob,?_⟩
  intro Y0 B0 C0 hY0 hB0 hC0 hB0m hB0c
  obtain ⟨D,hD⟩ := local_covariance_witness_exists P F hF hle hnull
    (fun t ω => extendOpenPath (Y ω) t) Y0 hY hY0
  refine ⟨D,hD,?_⟩
  intro j d hd hdj
  have hsubset : Icc (0:ℝ) d ⊆ Icc 0 (c j) := fun r hr => ⟨hr.1,hr.2.trans hdj⟩
  let hAdm := fun ω => (hAm j ω).mono hsubset
  let hAdc := fun ω => (hAc j ω).mono hsubset
  have hArdm ω := (hArmono j ω).mono hsubset
  have hArdc ω := (hArc j ω).mono hsubset
  have hμd ω :
      (intervalStieltjes 0 d hd (Ar ω) (hArdm ω)
        (fun r hr => (hArdc ω r hr).mono inter_subset_left)).measure =
      (intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hAdm ω)
        (fun r hr => (hAdc ω r hr).mono inter_subset_left)).measure := by
    apply interval_stieltjes_measure_congr_add_const 0 d hd
      (fun r => A (realTimeClamp r) ω) (Ar ω) (hAdm ω) (hArdm ω)
      (fun r hr => (hAdc ω r hr).mono inter_subset_left)
      (fun r hr => (hArdc ω r hr).mono inter_subset_left) 0
    intro r hr
    simpa only [add_zero] using hAr j ω r (hsubset hr)
  have hHi : ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2)
      (intervalStieltjes 0 (c j) (hc j).le (Ar ω) (hArmono j ω)
        (fun r hr => (hArc j ω r hr).mono inter_subset_left)).measure := by
    simpa only [hμ] using hi j
  have hHp := progressive_restricted_square_energy P (c j) d hd hdj Ar (hArmono j) (hArc j)
    hArdm hArdc hArm (fun r => F (realTimeClamp r)) (fun r => hle _) H (hH j) hHi
  simp only [hμd] at hHp
  have hHj := progressive_finite_square_energy P (c j) (hc j).le Ar (hArmono j) (hArc j) hArm
    (fun r => F (realTimeClamp r)) (fun r => hle _) H (hH j) hHi
  simp only [hμ] at hHj
  let μj := fun ω => (intervalStieltjes 0 (c j) (hc j).le (fun r => A (realTimeClamp r) ω) (hAm j ω)
    (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure
  let J := fun n ω r => ∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r
  have hJi n ω : MemLp (J n ω) 2 (μj ω) := by
    letI : IsFiniteMeasure (μj ω) := intervalStieltjes_finite _ _ _ _ _ _
    apply memLp_finsetSum
    intro i hi
    exact (memLp_const (V n i ω)).indicator measurableSet_Ico
  have hEi n : ∀ᵐ ω ∂P, Integrable (fun r => (J n ω r-H (ω,r))^2) (μj ω) := by
    filter_upwards [hHj.1] with ω hω
    have hh := (hJi n ω).sub hω
    exact (memLp_two_iff_integrable_sq hh.aestronglyMeasurable).1 hh
  have hpd := stieltjes_error_probability_restriction P (c j) d hd hdj
    (fun ω r => A (realTimeClamp r) ω) (hAm j) hAdm
    (fun ω r hr => (hAc j ω r hr).mono inter_subset_left)
    (fun ω r hr => (hAdc ω r hr).mono inter_subset_left)
    (fun n ω r => (J n ω r-H (ω,r))^2) hEi (fun n ω r => sq_nonneg _) (hprob j)
  let Hc := fun ω r => H (ω,(projIcc 0 (c j) (hc j).le r:ℝ))
  letI : Fact (0 ≤ c j) := ⟨(hc j).le⟩
  have hHcm : Measurable (fun z : Ω × ℝ => Hc z.1 z.2) := by
    have hq : Measurable (fun z : Ω × ℝ => (z.1,projIcc 0 (c j) (hc j).le z.2)) :=
      measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
    exact ((hH j).mono (progressive_space_le_product
      (fun t : Icc (0:ℝ) (c j) => F (realTimeClamp t.val)) (fun t => hle _)) le_rfl).comp hq
  let μd := fun ω => (intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hAdm ω)
    (fun r hr => (hAdc ω r hr).mono inter_subset_left)).measure
  have heHc ω : Hc ω =ᵐ[μd ω] (fun r => H (ω,r)) := by
    filter_upwards [interval_stieltjes_ae_mem_Ioc 0 d hd (fun r => A (realTimeClamp r) ω) (hAdm ω)
      (fun r hr => (hAdc ω r hr).mono inter_subset_left)] with r hr
    have hpr : (projIcc 0 (c j) (hc j).le r:ℝ) = r :=
      congrArg Subtype.val (projIcc_of_mem (hc j).le ⟨hr.1.le,hr.2.trans hdj⟩)
    dsimp only [Hc]
    rw [hpr]
  have hHci : ∀ᵐ ω ∂P, MemLp (Hc ω) 2 (μd ω) :=
    hHp.1.mono (fun ω hh => (memLp_congr_ae (heHc ω).symm).mp hh)
  have hpc : ∀ δ > 0, Tendsto (fun n => P {ω | δ ≤ ∫ r, (J n ω r-Hc ω r)^2 ∂μd ω}) atTop (𝓝 0) := by
    have heq n ω : (∫ r, (J n ω r-Hc ω r)^2 ∂μd ω) = ∫ r, (J n ω r-H (ω,r))^2 ∂μd ω := by
      apply integral_congr_ae
      exact (heHc ω).mono (fun r hr => by change (J n ω r-Hc ω r)^2 = (J n ω r-H (ω,r))^2; rw [hr])
    intro δ hδ
    simpa only [heq] using hpd δ hδ
  obtain ⟨ν,hν,hνac,hνint,heD⟩ := ito_approximation_covariance_at_time P F hF hle hnull X A hX hA
    c (fun n => (hc n).le) hcm.monotone hcT hct hcut hcc hAm hAc N u V hu hub
    (fun n i hi => (hVm n i hi).1) (fun n i hi => (hVm n i hi).2)
    Z Y hZ hY hlim Y0 B0 C0 D hY0 hB0 hC0 hD Hc d hd
    ((EReal.coe_le_coe hdj).trans_lt (hcT j)) hAdm hAdc
    (fun ω => hHcm.comp measurable_prodMk_left)
    (fun ω => (hB0m j ω).mono hsubset) (fun ω => (hB0c j ω).mono hsubset) hHci hpc
  refine ⟨ν,hν,?_⟩
  filter_upwards [heD,hνac] with ω hDω hac
  exact hDω.trans (signed_integral_congr_of_absolute_continuity (μd ω) (ν ω) hac (heHc ω))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_integral_constructed_with_universal_covariance
