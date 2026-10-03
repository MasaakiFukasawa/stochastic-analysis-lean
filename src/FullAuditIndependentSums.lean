import FullAuditBrownianMartingaleExercise

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

def prefixSigma {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ i : Fin n, (borel ℝ).comap (Z i.val)

theorem prefix_sigma_le {Ω : Type*} {m : MeasurableSpace Ω}
    (Z : ℕ → Ω → ℝ) (hm : ∀ i, Measurable[m] (Z i)) (n : ℕ) : prefixSigma Z n ≤ m :=
  iSup_le fun i => (hm i.val).comap_le

theorem prefix_sigma_mono {Ω : Type*} (Z : ℕ → Ω → ℝ) : Monotone (prefixSigma Z) := by
  intro n k hnk
  apply iSup_le
  intro i
  exact le_iSup_of_le (⟨i.val,lt_of_lt_of_le i.isLt hnk⟩ : Fin k) le_rfl

theorem prefix_variable_measurable {Ω : Type*} (Z : ℕ → Ω → ℝ) (n i : ℕ) (hi : i < n) :
    Measurable[prefixSigma Z n] (Z i) :=
  Measurable.of_comap_le (le_iSup (fun j : Fin n => (borel ℝ).comap (Z j.val)) ⟨i,hi⟩)

/-- Independence is with the entire finite past, not just each separate coordinate. -/
theorem independent_future_prefix {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) (Z : ℕ → Ω → ℝ) (hm : ∀ i, Measurable[m] (Z i))
    (hi : iIndepFun Z P) (n k : ℕ) (hnk : n ≤ k) :
    IndepFun (Z k) (fun ω (j : Fin n) => Z j.val ω) P := by
  have hd : Disjoint ({k} : Finset ℕ) (Finset.range n) := by
    simp only [Finset.disjoint_singleton_left,Finset.mem_range,not_lt]
    exact hnk
  have h := hi.indepFun_finset {k} (Finset.range n) hd hm
  have hc := h.comp (measurable_pi_apply (⟨k,Finset.mem_singleton_self k⟩ : ({k} : Finset ℕ)))
    (Measurable.of_eval (fun j : Fin n => measurable_pi_apply (⟨j.val,Finset.mem_range.mpr j.isLt⟩ : Finset.range n)))
  exact hc

/-- Conditional expectation of a centered future variable given the whole prefix. -/
theorem independent_prefix_conditional_zero {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hm : ∀ i, Measurable[m] (Z i)) (hi : iIndepFun Z P)
    (hz : ∀ i, ∫ ω, Z i ω ∂P = 0) (n k : ℕ) (hnk : n ≤ k) :
    P[Z k | prefixSigma Z n] =ᵐ[P] 0 := by
  have hh : prefixSigma Z n = MeasurableSpace.comap (fun ω (j : Fin n) => Z j.val ω) inferInstance := by
    apply le_antisymm
    · apply iSup_le
      intro j
      exact ((measurable_pi_apply j).comp
        (show Measurable[MeasurableSpace.comap (fun ω (j : Fin n) => Z j.val ω) inferInstance]
          (fun ω (j : Fin n) => Z j.val ω) from Measurable.of_comap_le le_rfl)).comap_le
    · letI : MeasurableSpace Ω := prefixSigma Z n
      exact (Measurable.of_eval (fun j : Fin n => prefix_variable_measurable Z n j.val j.isLt)).comap_le
  rw [hh]
  have h := condExp_indep_eq (hm k).comap_le
    ((Measurable.of_eval (fun j : Fin n => hm j.val)).comap_le)
    (show StronglyMeasurable[MeasurableSpace.comap (Z k) inferInstance] (Z k) from
      (Measurable.of_comap_le le_rfl).stronglyMeasurable)
    (independent_future_prefix P Z hm hi n k hnk)
  simpa only [hz,Pi.zero_def] using h

noncomputable def partialSum {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range n, Z i ω

theorem partial_sum_adapted {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ) :
    Measurable[prefixSigma Z n] (partialSum Z n) := by
  unfold partialSum
  exact Finset.measurable_sum (Finset.range n) (fun i hi => prefix_variable_measurable Z n i (Finset.mem_range.mp hi))

theorem partial_sum_memLp {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    (Z : ℕ → Ω → ℝ) (p : ℝ≥0∞) (hp : ∀ i, MemLp (Z i) p P) (n : ℕ) :
    MemLp (partialSum Z n) p P := by
  unfold partialSum
  exact memLp_finsetSum (Finset.range n) (fun i _ => hp i)

/-- The partial-sum martingale follows by induction from independent centered increments. -/
theorem independent_partial_sum_martingale {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hm : ∀ i, Measurable[m] (Z i)) (hi : iIndepFun Z P)
    (hint : ∀ i, Integrable (Z i) P) (hz : ∀ i, ∫ ω, Z i ω ∂P = 0)
    (n k : ℕ) (hnk : n ≤ k) :
    P[partialSum Z k | prefixSigma Z n] =ᵐ[P] partialSum Z n := by
  induction k,hnk using Nat.le_induction with
  | base =>
    exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable (prefix_sigma_le Z hm n)
      (partial_sum_adapted Z n).stronglyMeasurable (integrable_finsetSum _ (fun i _ => hint i)))
  | succ k hnk ih =>
    have he : partialSum Z (k+1) = partialSum Z k + Z k := by
      funext ω
      exact Finset.sum_range_succ (fun i => Z i ω) k
    rw [he]
    have ha := condExp_add (integrable_finsetSum (Finset.range k) (fun i _ => hint i)) (hint k) (prefixSigma Z n)
    have hz := independent_prefix_conditional_zero P Z hm hi hz n k hnk
    change P[partialSum Z k + Z k | prefixSigma Z n] =ᵐ[P]
      P[partialSum Z k | prefixSigma Z n]+P[Z k | prefixSigma Z n] at ha
    filter_upwards [ha,ih,hz] with ω ha ih hz
    simpa only [Pi.add_apply,ih,hz,Pi.zero_apply,add_zero] using ha
end Asakura.FullAudit
