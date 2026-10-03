import Chapter12VectorWienerConstruction
import Chapter12GaussianMartingaleTerminal

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Gaussianity of the vector integral is derived from its actual coordinate
integrals, rather than assuming independence of their terminal values. -/
theorem vector_actual_wiener_gaussian_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (W : PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀ f : PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : Fin d → HalfClosedTime → Ω → ℝ,
      ∃ hN : ∀ i, ContinuousM2Witness P B.F (N i),
        (∀ i, ItoCovarianceFormula P B.F (B.W i) (fun z => f i z.2) (N i)) ∧
        W f = ∑ i, ((hN i).moment ⊤).toLp (N i ⊤))
    (f : PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))))) :
    HasLaw (W f : Ω → ℝ) (gaussianReal 0 ⟨‖f‖^2,sq_nonneg _⟩) P := by
  obtain ⟨N,hN,hNI,he⟩ := hW f
  let M := fun t w => ∑ i, N i t w
  have hM : ContinuousM2Witness P B.F M := finite_sum_continuous_m2 P B.F B.mono B.le N hN
  obtain ⟨u,hu,hum,hut⟩ := exists_seq_strictMono_tendsto'
    (show (⊥ : HalfClosedTime)<⊤ from (show (0:EReal)<⊤ by simp))
  have huc (t : HalfClosedTime) (ht : t < ⊤) : ∃ n, t < u n :=
    (hut.eventually (lt_mem_nhds ht)).exists
  have hNl i := continuous_m2_is_local P B.F B.mono B.le u hu.monotone
    (fun n => (hum n).2) huc (N i) (hN i)
  have hprod i j R (hR : 0 ≤ R) : IntervalIntegrable (fun s => f i s*f j s) volume 0 R := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
    have hi (k : Fin d) : MemLp (f k : ℝ → ℝ) 2 (volume.restrict (Ioc 0 R)) :=
      (Lp.memLp (f k)).mono_measure (Measure.restrict_mono (fun _ hs => hs.1) le_rfl)
    exact (hi i).integrable_mul (hi j)
  have hlaw (t : HalfClosedTime) (ht : t < ⊤) : HasGaussianLaw (M t) P ∧ (∫ w,M t w ∂P)=0 := by
    obtain ⟨R,hR,_,hr⟩ := finite_closed_time_real t ht
    have h := integrable_deterministic_noise_law P B (fun i => (f i : ℝ → ℝ))
      (fun i => (Lp.stronglyMeasurable (f i)).measurable)
      (fun i b hb => (deterministic_L2_local_integrability (f i) b hb).1)
      hprod N hNl hNI R hR
    rw [hr] at h
    exact ⟨h.hasGaussianLaw,by simpa only [integral_id_gaussianReal] using h.integral_eq⟩
  have heq : W f = (hM.moment ⊤).toLp (M ⊤) := by
    rw [he]
    apply Lp.ext
    refine (Lp.coeFn_finsetSum _ _).trans ?_
    refine (eventuallyEq_sum (fun i _ => ((hN i).moment ⊤).coeFn_toLp)).trans ?_
    filter_upwards [(hM.moment ⊤).coeFn_toLp] with w hw
    simpa only [Finset.sum_apply, M] using hw.symm
  obtain ⟨hg,hm⟩ := centered_gaussian_m2_terminal P B.F B.mono B.le M hM hlaw
  rw [← heq] at hg hm
  refine ⟨(Lp.memLp (W f)).aestronglyMeasurable.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,hm,Asakura.L2_variance_inner,hm,
    zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,W.inner_map_map,real_inner_self_eq_norm_sq]
  congr 1
  apply NNReal.eq
  exact max_eq_left (sq_nonneg _)

end Asakura.Chapter12
