import FullAuditSignedFunctional
import Chapter1WrittenL1

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- The finite nonnegative matrix estimate in the manuscript's proof. Zero-mass
columns may have sum zero, so the hypothesis is at most one. -/
theorem variation_matrix_bound {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (c : ι → κ → ℝ) (v : κ → ℝ)
    (hc : ∀ i ∈ I, ∀ j ∈ J, 0 ≤ c i j)
    (hs : ∀ j ∈ J, ∑ i ∈ I, c i j ≤ 1) :
    ∑ i ∈ I, |∑ j ∈ J, c i j * v j| ≤ ∑ j ∈ J, |v j| := by
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, c i j * |v j| := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ j ∈ J, |c i j * v j| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [abs_mul, abs_of_nonneg (hc i hi j hj)]
    _ = ∑ j ∈ J, (∑ i ∈ I, c i j) * |v j| := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum fun j hj => by
      simpa using mul_le_mul_of_nonneg_right (hs j hj) (abs_nonneg (v j))

/-- The signed integral depends only on the P-equivalence class when variation
is dominated by a finite multiple of P. -/
theorem signedIntegralRaw_congr_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : SignedMeasure Ω) (c : ENNReal) (hc : c ≠ ∞)
    (hdom : ν.totalVariation ≤ c • P) {f g : Ω → ℝ} (hfg : f =ᵐ[P] g) :
    signedIntegralRaw ν f = signedIntegralRaw ν g := by
  have hp : ν.toJordanDecomposition.posPart ≤ c • P :=
    (show ν.toJordanDecomposition.posPart ≤ ν.totalVariation from
      fun A => le_add_right le_rfl).trans hdom
  have hn : ν.toJordanDecomposition.negPart ≤ c • P :=
    (show ν.toJordanDecomposition.negPart ≤ ν.totalVariation from
      fun A => le_add_left le_rfl).trans hdom
  unfold signedIntegralRaw
  rw [integral_congr_ae ((Measure.absolutelyContinuous_of_le_smul hp).ae_eq hfg),
    integral_congr_ae ((Measure.absolutelyContinuous_of_le_smul hn).ae_eq hfg)]

/-- Connect the manuscript's L1 conditional-expectation convergence theorem to
convergence of signed integrals; no almost-everywhere subsequence is selected. -/
theorem signedIntegral_condExp_tendsto {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : SignedMeasure Ω)
    (c : ENNReal) (hc : c ≠ ∞) (hdom : ν.totalVariation ≤ c • P)
    (G : ℕ → MeasurableSpace Ω) (hG : Monotone G) (hle : ∀ n, G n ≤ m)
    (hgen : (⨆ n, G n) = m) {X : Ω → ℝ} (hmX : Measurable X) (hX : Integrable X P) :
    Tendsto (fun n => signedIntegralRaw ν P[X | G n]) atTop (𝓝 (signedIntegralRaw ν X)) := by
  have hconv := (Asakura.Chapter1Written.conditional_L1_written G hle hmX hX).1 hG
  rw [hgen, condExp_of_stronglyMeasurable le_rfl hmX.stronglyMeasurable hX] at hconv
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => P[X | G n]) (fun n => (memLp_one_iff_integrable.mpr integrable_condExp)) X (memLp_one_iff_integrable.mpr hX)).mpr hconv
  have ht := signedIntegralRaw_tendsto_L1 P ν c hc hdom _ _ hLp
  have he (f : Ω → ℝ) (hf : MemLp f 1 P) :
      signedIntegralRaw ν (hf.toLp f) = signedIntegralRaw ν f :=
    signedIntegralRaw_congr_ae P ν c hc hdom hf.coeFn_toLp
  simpa only [he] using ht


/-- The indicator functions of a finite partition sum to one pointwise. -/
theorem partition_indicator_sum {Ω : Type*} (J : Finpartition (univ : Set Ω)) (ω : Ω) :
    ∑ E ∈ J.parts, E.indicator (fun _ => (1:ℝ)) ω = 1 := by
  classical
  have hu : (⋃ E ∈ J.parts, E) = univ := by
    rw [← Finset.sup_set_eq_biUnion]
    exact J.sup_parts
  obtain ⟨E, hE, hω⟩ := mem_iUnion₂.mp (show ω ∈ ⋃ E ∈ J.parts, E by rw [hu]; trivial)
  rw [Finset.sum_eq_single E]
  · simp [hω]
  · intro F hF hFE
    have hωF : ω ∉ F := fun h => Set.disjoint_left.mp (J.disjoint hF hE hFE) h hω
    simp [hωF]
  · exact fun h => (h hE).elim

/-- The conditional cell coefficients have total at most one (zero on a null cell). -/
theorem partition_coefficients_sum_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (J : Finpartition (univ : Set Ω))
    (hJ : ∀ F ∈ J.parts, MeasurableSet F) (E : Set Ω) :
    ∑ F ∈ J.parts, (P.real E)⁻¹ * ∫ ω in E, F.indicator (fun _ => (1:ℝ)) ω ∂P ≤ 1 := by
  classical
  rw [← Finset.mul_sum, ← integral_finsetSum]
  · simp only [partition_indicator_sum, setIntegral_const, smul_eq_mul, mul_one]
    by_cases hz : P.real E = 0
    · simp [hz]
    · simp [hz]
  · intro F hF
    exact (integrable_const _).indicator (hJ F hF)

/-- Normalizing total variation supplies exactly the probability measure and
finite domination constant used in the manuscript. -/
theorem variation_normalization {Ω : Type*} [MeasurableSpace Ω]
    (ν : SignedMeasure Ω) (hν : ν.totalVariation univ ≠ 0) :
    IsProbabilityMeasure ((ν.totalVariation univ)⁻¹ • ν.totalVariation) ∧
    ν.totalVariation = (ν.totalVariation univ) •
      ((ν.totalVariation univ)⁻¹ • ν.totalVariation) := by
  have hfin : ν.totalVariation univ ≠ ∞ := measure_ne_top _ _
  constructor
  · constructor
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hν hfin
  · rw [smul_smul, ENNReal.mul_inv_cancel hν hfin, one_smul]


/-- Sum of the absolute signed integrals of all approximated indicators is
bounded by the discrete variation of the approximating partition. -/
theorem partitionMean_variation_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : SignedMeasure Ω)
    (J F : Finpartition (univ : Set Ω))
    (hJ : ∀ E ∈ J.parts, MeasurableSet E) (hF : ∀ E ∈ F.parts, MeasurableSet E) :
    ∑ A ∈ F.parts, |signedIntegralRaw ν (partitionMean P J (A.indicator (fun _ => (1:ℝ))))|
      ≤ ∑ E ∈ J.parts, |ν E| := by
  simp_rw [signedIntegralRaw_partitionMean P ν J hJ]
  apply variation_matrix_bound
  · intro A hA E hE
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun ω => indicator_nonneg (fun _ _ => zero_le_one) ω)
  · intro E hE
    exact partition_coefficients_sum_le P F hF E

/-- A finite partition's variation is bounded by every limit of the discrete
variations. This is the manuscript's limit step before taking a supremum. -/
theorem partition_variation_le_limit {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : SignedMeasure Ω)
    (c : ENNReal) (hc : c ≠ ∞) (hdom : ν.totalVariation ≤ c • P)
    (J : ℕ → Finpartition (univ : Set Ω))
    (hJ : ∀ n, ∀ E ∈ (J n).parts, MeasurableSet E)
    (hG : Monotone (fun n => MeasurableSpace.generateFrom ((J n).parts : Set (Set Ω))))
    (hgen : (⨆ n, MeasurableSpace.generateFrom ((J n).parts : Set (Set Ω))) = m)
    (L : ℝ) (hL : Tendsto (fun n => ∑ E ∈ (J n).parts, |ν E|) atTop (𝓝 L))
    (F : Finpartition (univ : Set Ω)) (hF : ∀ A ∈ F.parts, MeasurableSet A) :
    ∑ A ∈ F.parts, |ν A| ≤ L := by
  have hconv (A : Set Ω) (hA : MeasurableSet A) :
      Tendsto (fun n => signedIntegralRaw ν (partitionMean P (J n) (A.indicator (fun _ => (1:ℝ)))))
        atTop (𝓝 (ν A)) := by
    have ht := signedIntegral_condExp_tendsto P ν c hc hdom
      (fun n => MeasurableSpace.generateFrom ((J n).parts : Set (Set Ω))) hG
      (fun n => MeasurableSpace.generateFrom_le (hJ n)) hgen
      (measurable_const.indicator hA) ((integrable_const (1:ℝ)).indicator hA)
    rw [signedIntegralRaw_indicator ν A hA] at ht
    apply ht.congr
    intro n
    exact (signedIntegralRaw_congr_ae P ν c hc hdom
      (partitionMean_condExp P (J n) (hJ n) ((integrable_const _).indicator hA))).symm
  apply le_of_tendsto_of_tendsto
    (tendsto_finset_sum F.parts (fun A hA => (hconv A (hF A hA)).abs)) hL
  exact Filter.Eventually.of_forall fun n => partitionMean_variation_bound P ν (J n) F (hJ n) hF

end Asakura.FullAudit
