import Chapter12MalliavinC1Chain
import Chapter12ExponentialApproximation
import Chapter12DominatedLpLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Extension to the unbounded exponential function. The two required Lp
moments are explicit and supplied by Gaussian exponential moments for stocks. -/
theorem closed_malliavin_exponential_chain {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (hgraph : (D.graph : Set (Lp ℝ p P × Lp H p P)) =
      closure (range (cylinderPair P W S hS hcore p hp)))
    (F : Lp ℝ p P) (U : Lp H p P) (hFU : (F,U) ∈ D.graph)
    (hi : MemLp (fun w => Real.exp (F w)) p P)
    (hdi : MemLp (fun w => Real.exp (F w) • U w) p P) :
    (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  let ε := fun n : ℕ => (1:ℝ)/(n+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let f := fun n w => cappedExp (ε n) (F w)
  let u := fun n w => cappedExpDeriv (ε n) (F w) • U w
  have hfm (n : ℕ) : Measurable (f n) := by
    exact (continuous_iff_continuousAt.mpr (fun x => (cappedExp_hasDerivAt (ε n) (hε n).le x).continuousAt)).measurable.comp
      (Lp.stronglyMeasurable F).measurable
  have hum (n : ℕ) : AEStronglyMeasurable (u n) P :=
    (((cappedExp_derivative_continuous (ε n) (hε n).le).measurable.comp
      (Lp.stronglyMeasurable F).measurable).aestronglyMeasurable).smul (Lp.aestronglyMeasurable U)
  have hfb (n : ℕ) : ∀ᵐ w ∂P, ‖f n w‖ ≤ ‖Real.exp (F w)‖ := by
    apply ae_of_all
    intro w
    have hb := cappedExp_bounds (ε n) (hε n) (F w)
    change |cappedExp (ε n) (F w)| ≤ |Real.exp (F w)|
    rw [abs_of_nonneg hb.1,abs_of_pos (Real.exp_pos _)]
    exact hb.2.1
  have hub (n : ℕ) : ∀ᵐ w ∂P, ‖u n w‖ ≤ ‖Real.exp (F w) • U w‖ := by
    apply ae_of_all
    intro w
    have hb := cappedExp_bounds (ε n) (hε n) (F w)
    dsimp only [u]
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg hb.2.2.1,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hb.2.2.2.1 (norm_nonneg _)
  have hfi n : MemLp (f n) p P := hi.of_le (hfm n).aestronglyMeasurable (hfb n)
  have hui n : MemLp (u n) p P := hdi.of_le (hum n) (hub n)
  have hc n : ((hfi n).toLp _,(hui n).toLp _) ∈ D.graph := by
    obtain ⟨hn,hgn⟩ := closed_malliavin_C1_chain P W S hS hcore p hp D hD hgraph F U hFU
      (cappedExp (ε n)) (cappedExpDeriv (ε n))
      (cappedExp_hasDerivAt (ε n) (hε n).le)
      (cappedExp_derivative_continuous (ε n) (hε n).le)
      (1/ε n) (by positivity) (fun x => (cappedExp_bounds (ε n) (hε n) x).2.2.2.2)
    have hv : lipschitzCompositionLp P p
        (bounded_derivative_lipschitz _ _ (cappedExp_hasDerivAt (ε n) (hε n).le)
          (1/ε n) (by positivity) (fun x => (cappedExp_bounds (ε n) (hε n) x).2.2.2.2)) F =
        (hfi n).toLp _ := by
      apply Lp.ext
      exact (lipschitzCompositionLp_coe P p _ F).trans (hfi n).coeFn_toLp.symm
    have hu : hn.toLp _ = (hui n).toLp _ := by
      apply Lp.ext
      exact hn.coeFn_toLp.trans (hui n).coeFn_toLp.symm
    rwa [hv,hu] at hgn
  have hv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hfi _ hi).mpr
    (dominated_Lp_limit P p (Fact.out : 1 ≤ p) hp f _ _ hi
      (fun n => (hfm n).aestronglyMeasurable) hi hfb
      (ae_of_all P fun w => (cappedExp_approximation (F w)).1))
  have hd := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hui _ hdi).mpr
    (dominated_Lp_limit P p (Fact.out : 1 ≤ p) hp u _ _ hdi hum hdi hub
      (ae_of_all P fun w => ((cappedExp_approximation (F w)).2).smul_const (U w)))
  exact hD.mem_of_tendsto (hv.prodMk_nhds hd) (Eventually.of_forall hc)

end Asakura.Chapter12
