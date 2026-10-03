import Chapter2WeightedCumulative
import Chapter2WeightedPaths
import Chapter2CumulativeAdapted
import Chapter2CumulativeTests
import Chapter2CumulativeSupport
import Chapter2RealOrthogonalVariation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The central orthogonal-complement argument in the density lemma.
All properties of the cumulative process are constructed from the integrand,
then A intersect M2 and signed-measure separation force the integrand to zero.
The representative has already been made finite-energy on every path. -/
theorem weighted_orthogonal_integrand_zero
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
    (henergy : ∀ ω, (∫⁻ r, ENNReal.ofReal (H (ω,projIcc 0 b hb.le r)^2)
      ∂(intervalStieltjes 0 b hb.le (A ω) (hA ω) (hr ω)).measure) < ∞)
    (horth : ∀ s t : Icc (0:ℝ) b, s ≤ t → ∀ Z : Ω → ℝ,
      Measurable[F s] Z → MemLp Z ∞ P →
      (∫ ω, ∫ r, ((Ico s.val t.val).indicator (fun _ => Z ω) r) * H (ω,projIcc 0 b hb.le r)
        ∂(intervalStieltjes 0 b hb.le (A ω) (hA ω) (hr ω)).measure ∂P) = 0) :
    H =ᵐ[(weightedPathMeasure P 0 b hb.le A hA hr hm).trim
      (progressive_space_le_product F hle)] 0 := by
  let κ := randomStieltjesKernel 0 b hb.le A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite 0 b hb.le A hA hr hm K hK
  letI (ω : Ω) : IsFiniteMeasure (intervalStieltjes 0 b hb.le (A ω) (hA ω) (hr ω)).measure :=
    intervalStieltjes_finite 0 b hb.le (A ω) (hA ω) (hr ω)
  letI (ω : Ω) : NullSingletonClass (κ ω) := interval_stieltjes_no_atoms_on 0 b hb.le (A ω) (hA ω) (hr ω) (hc ω)
  let g := fun ω r => H (ω,projIcc 0 b hb.le r)
  let N := fun t : Icc (0:ℝ) b => fun ω => ∫ r in Iic t.val, g ω r ∂κ ω
  have hHp : Measurable H := hH.mono (progressive_space_le_product F hle) le_rfl
  have hg (ω) : Measurable (g ω) := hHp.comp (measurable_const.prodMk continuous_projIcc.measurable)
  have hpath (ω) := weighted_cumulative_path_properties 0 b hb.le (A ω) (hA ω) (hr ω) (hc ω)
    (g ω) (hg ω) (henergy ω)
  have hgi (ω) : Integrable (g ω) (κ ω) :=
    (hpath ω).1.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hNad (t) : Measurable[F t] (N t) :=
    cumulative_stieltjes_adapted 0 b hb.le F hF A hA hr had K hK H hH t
  have hN2 (t) : MemLp (N t) 2 P :=
    (weighted_progressive_cumulative_memLp_two P 0 b hb.le A hA hr hm K hK0 hK F hle H hH hH2 t.val).1
  have hNc (ω) : Continuous (fun t => N t ω) := (hpath ω).2.1.comp continuous_subtype_val
  have hNv (ω) : ∃ U V : Icc (0:ℝ) b → ℝ, Monotone U ∧ Monotone V ∧ ∀ t, N t ω = U t-V t := by
    obtain ⟨U,V,_,_,hU,hV,hUV⟩ := (hpath ω).2.2.2
    exact ⟨fun t => U t.val,fun t => V t.val,hU.comp (Subtype.mono_coe _),hV.comp (Subtype.mono_coe _),fun t => hUV t.val⟩
  have hNz : N ⊥ =ᵐ[P] 0 := .of_forall fun ω => (hpath ω).2.2.1
  have hNo : ∀ s t, s ≤ t → ∀ Z : Ω → ℝ, Measurable[F s] Z → MemLp Z ∞ P →
      (∫ ω, Z ω * (N t ω-N s ω) ∂P) = 0 := by
    intro s t hst Z hZ hZ2
    have he (ω) := cumulative_increment_elementary_test (κ ω) (g ω) (hgi ω) s.val t.val (Z ω) hst
    simp only [N,he]
    exact horth s t hst Z hZ hZ2
  have hzero := real_finite_variation_zero_of_orthogonal_past_tests P b hb F hF hle N hNad hN2 hNc hNv hNz hNo
  have hgz : ∀ᵐ ω ∂P, g ω =ᵐ[κ ω] 0 := by
    filter_upwards [hzero] with ω hω
    apply integrand_zero_of_interval_cumulative_zero 0 b hb.le (κ ω)
      (interval_stieltjes_ae_mem_Ioc 0 b hb.le (A ω) (hA ω) (hr ω)) (g ω) (hgi ω)
    intro t ht
    exact hω ⟨t,ht⟩
  apply ae_eq_trim_of_measurable (progressive_space_le_product F hle) hH measurable_const
  have hproj : Measurable (fun p : Ω × ℝ => (p.1,projIcc 0 b hb.le p.2)) :=
    measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  apply (ae_map_iff hproj.aemeasurable (measurableSet_eq_fun hHp measurable_const)).2
  exact Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun (hHp.comp hproj) measurable_const) hgz

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_orthogonal_integrand_zero
