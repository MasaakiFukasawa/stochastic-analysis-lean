import Chapter12BoundedLpConvergence

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Conditional expectation preserves the bound used in the manuscript. -/
theorem conditional_L2_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G ≤ m)
    (U : Lp ℝ 2 P) (C : ℝ) (hU : ∀ᵐ ω ∂P, |U ω| ≤ C) :
    ∀ᵐ ω ∂P, |(condExpL2 ℝ ℝ hG U : Lp ℝ 2 P) ω| ≤ C := by
  have he := (Lp.memLp U).condExpL2_ae_eq_condExp (𝕜 := ℝ) hG
  have hU' : (Lp.memLp U).toLp (U : Ω → ℝ) = U :=
    Lp.ext (Lp.memLp U).coeFn_toLp
  rw [hU'] at he
  filter_upwards [he,ae_bdd_abs_condExp_of_ae_bdd_abs (m := G) hU] with ω hω hb
  rwa [hω]

/-- Bounded variables: finite increasing information approximates in every
finite Lp, starting with the manuscript's proved L2 convergence. -/
theorem conditional_upward_bounded_Lp {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → MeasurableSpace Ω)
    (hG : Monotone G) (hle : ∀ n, G n ≤ m)
    (U : Lp ℝ 2 P) (hU : AEStronglyMeasurable[⨆ n,G n] U P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, |U ω| ≤ C)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    Tendsto (fun n => eLpNorm
      (fun ω => (condExpL2 ℝ ℝ (hle n) U : Lp ℝ 2 P) ω-U ω) p P)
      atTop (𝓝 0) := by
  have htop : (⨆ n,G n) ≤ m := iSup_le hle
  letI : Fact ((⨆ n,G n) ≤ m) := ⟨htop⟩
  have he : (condExpL2 ℝ ℝ htop U : Lp ℝ 2 P) = U :=
    (lpMeas ℝ ℝ (⨆ n,G n) 2 P).starProjection_eq_self_iff.mpr hU
  have ht := Asakura.Chapter1Written.conditional_upward_L2_written G hG hle U
  rw [he] at ht
  exact bounded_L2_to_Lp P p hp hpt _ U ht C hC
    (fun n => conditional_L2_bound P (G n) (hle n) U C hb) hb

end Asakura.Chapter12
