import Chapter12WienerItoConstruction
import Chapter10IntegrableNoiseLaw
import Chapter2M2TimeContinuity
import Chapter12WienerGaussianClosure

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Local integrability of a deterministic L2 time function and its square
supplies the hypotheses of the previously checked Gaussian integral law. -/
theorem deterministic_L2_local_integrability
    (f : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) (R : ℝ) (hR : 0 ≤ R) :
    IntervalIntegrable (f : ℝ → ℝ) volume 0 R ∧
      IntervalIntegrable (fun s => f s*f s) volume 0 R := by
  have hi : MemLp (f : ℝ → ℝ) 2 (volume.restrict (Ioc 0 R)) :=
    (Lp.memLp f).mono_measure (Measure.restrict_mono (fun _ hs => hs.1) le_rfl)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr (hi.integrable (by norm_num)),?_⟩
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
  simpa only [IntegrableOn,Real.norm_eq_abs,← pow_two,sq_abs] using hi.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)

/-- The Gaussian law of the constructed Wiener integral follows from the
finite-time deterministic bracket law and an actual L2 terminal limit. -/
theorem actual_wiener_gaussian_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (W : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ f : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))),
      ∃ M : HalfClosedTime → Ω → ℝ, ∃ hM : ContinuousM2Witness P B.F M,
        ItoCovarianceFormula P B.F (B.W 0) (fun z => f z.2) M ∧
        W f = (hM.moment ⊤).toLp (M ⊤))
    (f : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) :
    HasLaw (W f : Ω → ℝ) (gaussianReal 0 ⟨‖f‖^2,sq_nonneg _⟩) P := by
  obtain ⟨M,hM,hMI,he⟩ := hW f
  obtain ⟨u,hu,hum,hut⟩ := exists_seq_strictMono_tendsto' (show (⊥ : HalfClosedTime)<⊤ from (show (0:EReal)<⊤ by simp))
  have huc (t : HalfClosedTime) (ht : t < ⊤) : ∃ n, t < u n :=
    (hut.eventually (lt_mem_nhds ht)).exists
  have hMl := continuous_m2_is_local P B.F B.mono B.le u hu.monotone (fun n => (hum n).2) huc M hM
  have hlaw (t : HalfClosedTime) (ht : t < ⊤) : HasGaussianLaw (M t) P ∧ (∫ w,M t w ∂P)=0 := by
    obtain ⟨R,hR,hRt,hr⟩ := finite_closed_time_real t ht
    have h := integrable_deterministic_noise_law P B (fun _ => (f : ℝ → ℝ))
      (fun _ => (Lp.stronglyMeasurable f).measurable)
      (fun _ b hb => (deterministic_L2_local_integrability f b hb).1)
      (fun _ _ b hb => (deterministic_L2_local_integrability f b hb).2)
      (fun _ => M) (fun _ => hMl) (fun j => by
        have hj : j = 0 := Subsingleton.elim _ _
        simpa only [hj] using hMI) R hR
    simp only [Fin.sum_univ_one,hr] at h
    exact ⟨h.hasGaussianLaw,by simpa only [integral_id_gaussianReal] using h.integral_eq⟩
  let Z := fun n => (hM.moment (u n)).toLp (M (u n))
  have hlim : Tendsto Z atTop (𝓝 ((hM.moment ⊤).toLp (M ⊤))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
      ((continuous_m2_time_l2_continuity P B.F B.mono B.le M hM ⊤).comp hut)
  have hg : HasGaussianLaw (W f : Ω → ℝ) P := by
    rw [he]
    apply Asakura.gaussian_L2_limit _ hlim
    intro n
    exact ((hlaw (u n) (hum n).2).1).congr (hM.moment (u n)).coeFn_toLp.symm
  have hm : (∫ w,W f w ∂P)=0 := by
    have hmean := Asakura.L2_mean_continuous.continuousAt.tendsto.comp hlim
    have hz n : (∫ w,Z n w ∂P)=0 :=
      (integral_congr_ae (hM.moment (u n)).coeFn_toLp).trans (hlaw (u n) (hum n).2).2
    change Tendsto (fun n => ∫ w,Z n w ∂P) atTop (𝓝 (∫ w,(hM.moment ⊤).toLp _ w ∂P)) at hmean
    simp only [hz] at hmean
    rw [he]
    exact tendsto_nhds_unique hmean tendsto_const_nhds
  refine ⟨(Lp.memLp (W f)).aestronglyMeasurable.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,hm,Asakura.L2_variance_inner,hm,zero_pow (by norm_num : (2:ℕ)≠0),
    sub_zero,W.inner_map_map,real_inner_self_eq_norm_sq]
  congr 1
  apply NNReal.eq
  exact max_eq_left (sq_nonneg _)

end Asakura.Chapter12
