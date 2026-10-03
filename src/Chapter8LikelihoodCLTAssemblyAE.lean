import Chapter8LikelihoodCLTAssembly

open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped Topology Matrix.Norms.Elementwise
namespace Asakura.Chapter8
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Likelihood equations holding almost surely suffice, as required for
identities between the actual stochastic integrals. -/
theorem likelihood_clt_assembly_ae {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℕ → Ω → EuclideanSpace ℝ ι)
    (J : ℕ → Ω → Matrix ι ι ℝ) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hX : TendstoInDistribution X atTop id (fun _ => P) (multivariateGaussian 0 S))
    (hmJ : ∀ n,Measurable (J n)) (hmY : ∀ n,AEMeasurable (Y n) P)
    (hJ : ∀ i j,TendstoInMeasure P (fun n ω => J n ω i j) atTop (fun _ => S i j))
    (he : ∀ n,∀ᵐ ω ∂P,(J n ω).det ≠ 0 →
      Y n ω=Matrix.toEuclideanCLM (𝕜 := ℝ) (J n ω)⁻¹ (X n ω)) :
    TendstoInDistribution Y atTop id (fun _ => P) (multivariateGaussian 0 S⁻¹) := by
  classical
  let Y' := fun n ω => if (J n ω).det≠0 then Matrix.toEuclideanCLM (𝕜 := ℝ) (J n ω)⁻¹ (X n ω) else Y n ω
  have heq n : Y' n=ᵐ[P] Y n := by
    filter_upwards [he n] with ω hω
    dsimp only [Y']
    split_ifs with h
    · exact (hω h).symm
    · rfl
  have hm n : AEMeasurable (Y' n) P := (hmY n).congr (heq n).symm
  have hh := likelihood_clt_assembly P X Y' J S hS hX hmJ hm hJ
    (fun n ω hn => by simp only [Y',if_pos hn])
  exact hh.congr heq Filter.EventuallyEq.rfl
end Asakura.Chapter8
