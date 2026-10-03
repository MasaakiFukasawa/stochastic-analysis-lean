import Chapter2WeightedDensity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 0 < b) [Fact (0 ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc 0 b))
    (hr : ∀ ω x, x ∈ Icc 0 b → ContinuousWithinAt (A ω) (Icc 0 b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (K : ℝ) (hK : ∀ ω, A ω b-A ω 0 ≤ K)
    (F : Icc (0:ℝ) b → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)

/-- Every element of the dense L2 span has an actual finite elementary
process representative, with its coefficients measurable at their starting
times. This connects Hilbert-space approximation to the process notation. -/
theorem weighted_span_finite_representation :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
    let μ := (weightedPathMeasure P 0 b hb.le A hA hr hm).trim
      (progressive_space_le_product F hle)
    let S : Set (Lp ℝ 2 μ) :=
      {J | ∃ (s t : Icc (0:ℝ) b) (Z : Ω → ℝ) (hZ : Measurable[F s] Z) (hZinf : MemLp Z ∞ P),
        J = weightedElementaryLp P b hb A hA hr hm K hK F hF hle s t Z hZ hZinf}
    ∀ J ∈ Submodule.span ℝ S, ∃ (n : ℕ) (a d : Fin n → Icc (0:ℝ) b) (G : Fin n → Ω → ℝ),
      (∀ i, a i ≤ d i) ∧ (∀ i, Measurable[F (a i)] (G i)) ∧ (∀ i, MemLp (G i) ∞ P) ∧
      (J : Ω × Icc (0:ℝ) b → ℝ) =ᵐ[μ]
        (fun p => ∑ i, (Ico (a i) (d i)).indicator (fun _ => G i p.1) p.2) := by
  classical
  letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
  intro μ S J hJ
  obtain ⟨n,c,z,hz⟩ := Submodule.mem_span_set'.1 hJ
  have hzmem (i : Fin n) := (z i).property
  choose a d G hGm hG he using hzmem
  refine ⟨n,a,(fun i => max (a i) (d i)),(fun i ω => c i*G i ω),
    (fun i => le_max_left _ _),(fun i => (hGm i).const_mul (c i)),
    (fun i => (hG i).const_mul (c i)),?_⟩
  have hei (i : Fin n) : ((z i).val : Ω × Icc (0:ℝ) b → ℝ) =ᵐ[μ]
      (fun p => (Ico (a i) (d i)).indicator (fun _ => G i p.1) p.2) := by
    rw [he i]
    exact (weighted_elementary_memLp_two P 0 b hb.le A hA hr hm K hK F hF hle
      (a i) (d i) (G i) (hGm i) (hG i)).coeFn_toLp
  have hs := Lp.coeFn_fun_finsetSum (μ := μ) Finset.univ (fun i => c i • (z i).val)
  rw [hz] at hs
  have hsm (i : Fin n) := Lp.coeFn_smul (μ := μ) (c i) (z i).val
  filter_upwards [hs,ae_all_iff.2 hei,ae_all_iff.2 hsm] with p hp hpi hps
  rw [hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hps i]
  change c i*((z i).val : Ω × Icc (0:ℝ) b → ℝ) p = _
  rw [hpi i]
  change c i*(Ico (a i) (d i)).indicator (fun _ => G i p.1) p.2 =
    (Ico (a i) (max (a i) (d i))).indicator (fun _ => c i*G i p.1) p.2
  by_cases had : a i ≤ d i
  · rw [max_eq_right had]
    by_cases ht : p.2 ∈ Ico (a i) (d i)
    · rw [indicator_of_mem ht,indicator_of_mem ht]
    · rw [indicator_of_notMem ht,indicator_of_notMem ht,mul_zero]
  · have hda : d i ≤ a i := (not_le.1 had).le
    simp only [Ico_eq_empty_of_le hda,max_eq_left hda,Ico_self,indicator_empty,mul_zero]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_span_finite_representation
