import Chapter2WeightedRepresentations
import Mathlib.Topology.Sequences

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

include hK hF

/-- Concrete finite-step approximants are selected from the proved dense
Hilbert subspace, and their square-error integrals tend to zero. -/
theorem weighted_L2_step_approximation
    (hc : ∀ ω, ContinuousOn (A ω) (Icc 0 b)) (hK0 : 0 ≤ K)
    (had : ∀ t : Icc (0:ℝ) b, Measurable[F t] (fun ω => A ω t.val))
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
    let μ := (weightedPathMeasure P 0 b hb.le A hA hr hm).trim
      (progressive_space_le_product F hle)
    ∀ (H : Ω × Icc (0:ℝ) b → ℝ), MemLp H 2 μ →
    ∃ (n : ℕ → ℕ) (a d : (k : ℕ) → Fin (n k) → Icc (0:ℝ) b)
      (G : (k : ℕ) → Fin (n k) → Ω → ℝ),
      (∀ k i, a k i ≤ d k i) ∧
      (∀ k i, Measurable[F (a k i)] (G k i)) ∧ (∀ k i, MemLp (G k i) ∞ P) ∧
      (∀ k, MemLp (fun p => (∑ i, (Ico (a k i) (d k i)).indicator (fun _ => G k i p.1) p.2)-H p) 2 μ) ∧
      Tendsto (fun k => ∫ p, ((∑ i, (Ico (a k i) (d k i)).indicator (fun _ => G k i p.1) p.2)-H p)^2 ∂μ)
        atTop (𝓝 0) := by
  classical
  letI : MeasurableSpace (Ω × Icc (0:ℝ) b) := progressiveSpace F
  intro μ H hH
  let S : Set (Lp ℝ 2 μ) :=
    {J | ∃ (s t : Icc (0:ℝ) b) (Z : Ω → ℝ) (hZ : Measurable[F s] Z) (hZinf : MemLp Z ∞ P),
      J = weightedElementaryLp P b hb A hA hr hm K hK F hF hle s t Z hZ hZinf}
  have hdense : Dense (Submodule.span ℝ S).carrier :=
    weighted_elementary_span_dense P b hb A hA hr hm K hK F hF hle hc hK0 had hnull
  obtain ⟨J,hJ,hlim⟩ := mem_closure_iff_seq_limit.1 (hdense (hH.toLp H))
  have hex (k) := weighted_span_finite_representation P b hb A hA hr hm K hK F hF hle (J k) (hJ k)
  choose n a d G hord hadapt hbound hrep using hex
  let R := fun k p => (∑ i, (Ico (a k i) (d k i)).indicator (fun _ => G k i p.1) p.2)-H p
  have he (k) : ((J k-hH.toLp H : Lp ℝ 2 μ) : Ω × Icc (0:ℝ) b → ℝ) =ᵐ[μ] R k := by
    filter_upwards [Lp.coeFn_sub (J k) (hH.toLp H),hrep k,hH.coeFn_toLp] with p hp hj hh
    change (J k-hH.toLp H : Lp ℝ 2 μ) p = _
    rw [hp]
    change J k p-(hH.toLp H : Lp ℝ 2 μ) p = _
    rw [hj,hh]
  have henergy (k) : (∫ p, R k p ^ 2 ∂μ) = ‖J k-hH.toLp H‖^2 := by
    calc
      _ = ∫ p, ((J k-hH.toLp H : Lp ℝ 2 μ) p)^2 ∂μ :=
        integral_congr_ae ((he k).symm.mono fun p hp => congrArg (fun r : ℝ => r^2) hp)
      _ = _ := by
        rw [← real_inner_self_eq_norm_sq,L2.inner_def]
        simp only [Real.inner_apply,pow_two]
  refine ⟨n,a,d,G,hord,hadapt,hbound,fun k => (Lp.memLp (J k-hH.toLp H)).ae_eq (he k),?_⟩
  change Tendsto (fun k => ∫ p, R k p^2 ∂μ) atTop (𝓝 0)
  simp_rw [henergy]
  simpa only [sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using
    (hlim.sub_const (hH.toLp H)).norm.pow 2

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_L2_step_approximation
