import Chapter2WeightedOrthogonality

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Remove the finite-energy-on-every-path assumption by the manuscript's
null-set modification and preserve all orthogonality tests. -/
theorem weighted_orthogonal_integrand_zero_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 0 < b) [Fact (0 ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc 0 b))
    (hr : ∀ ω x, x ∈ Icc 0 b → ContinuousWithinAt (A ω) (Icc 0 b ∩ Ici x) x)
    (hc : ∀ ω, ContinuousOn (A ω) (Icc 0 b))
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ ω, A ω b-A ω 0 ≤ K)
    (F : Icc (0:ℝ) b → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (had : ∀ t : Icc (0:ℝ) b, Measurable[F t] (fun ω => A ω t.val))
    (H : Ω × Icc (0:ℝ) b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (hH2 : letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
      MemLp H 2 ((weightedPathMeasure P 0 b hb.le A hA hr hm).trim
        (progressive_space_le_product F hle)))
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N)
    (horth : ∀ s t : Icc (0:ℝ) b, s ≤ t → ∀ Z : Ω → ℝ,
      Measurable[F s] Z → MemLp Z ∞ P →
      (∫ ω, ∫ r, ((Ico s.val t.val).indicator (fun _ => Z ω) r) * H (ω,projIcc 0 b hb.le r)
        ∂(intervalStieltjes 0 b hb.le (A ω) (hA ω) (hr ω)).measure ∂P) = 0) :
    H =ᵐ[(weightedPathMeasure P 0 b hb.le A hA hr hm).trim
      (progressive_space_le_product F hle)] 0 := by
  let κ := randomStieltjesKernel 0 b hb.le A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite 0 b hb.le A hA hr hm K hK
  let μ := (weightedPathMeasure P 0 b hb.le A hA hr hm).trim (progressive_space_le_product F hle)
  obtain ⟨J,hJ,hJH,hJE⟩ := progressive_L2_finite_path_representative P 0 b hb.le A hA hr hm K hK F hle hnull H hH hH2
  have hJ2 : letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
      MemLp J 2 μ := (memLp_congr_ae hJH).2 hH2
  have hHp : Measurable H := hH.mono (progressive_space_le_product F hle) le_rfl
  have hJp : Measurable J := hJ.mono (progressive_space_le_product F hle) le_rfl
  have hproj : Measurable (fun p : Ω × ℝ => (p.1,projIcc 0 b hb.le p.2)) :=
    measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  have hsec : ∀ᵐ ω ∂P, (fun r => J (ω,projIcc 0 b hb.le r)) =ᵐ[κ ω]
      (fun r => H (ω,projIcc 0 b hb.le r)) := by
    apply Measure.ae_ae_of_ae_compProd (μ := P) (κ := κ)
      (p := fun p : Ω × ℝ => J (p.1,projIcc 0 b hb.le p.2) = H (p.1,projIcc 0 b hb.le p.2))
    exact (ae_map_iff hproj.aemeasurable (measurableSet_eq_fun hJp hHp)).1 (ae_eq_of_ae_eq_trim hJH)
  have ho : ∀ s t : Icc (0:ℝ) b, s ≤ t → ∀ Z : Ω → ℝ,
      Measurable[F s] Z → MemLp Z ∞ P →
      (∫ ω, ∫ r, ((Ico s.val t.val).indicator (fun _ => Z ω) r) * J (ω,projIcc 0 b hb.le r)
        ∂κ ω ∂P) = 0 := by
    intro s t hst Z hZ hZ2
    calc
      _ = ∫ ω, ∫ r, ((Ico s.val t.val).indicator (fun _ => Z ω) r) * H (ω,projIcc 0 b hb.le r) ∂κ ω ∂P := by
        apply integral_congr_ae
        filter_upwards [hsec] with ω hω
        apply integral_congr_ae
        filter_upwards [hω] with r hr
        rw [hr]
      _ = 0 := horth s t hst Z hZ hZ2
  have hz := weighted_orthogonal_integrand_zero P b hb A hA hr hc hm K hK0 hK F hF hle had J hJ hJ2 hJE ho
  exact hJH.symm.trans hz

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_orthogonal_integrand_zero_ae
