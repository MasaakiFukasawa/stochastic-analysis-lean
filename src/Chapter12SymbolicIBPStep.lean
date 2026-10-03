import Chapter12SymbolicProductBranches
import Chapter12GaussianJetIntegration

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

noncomputable def symbolicIBPBranchJet {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1))
    (ds : List (Fin e)) (gs : List (SymbolicGaussianFactor (e+1))) : GaussianJet (n+1) :=
  GaussianJet.finsetSum Finset.univ (fun i => ((u i).iteratedPartial (ds.map a)).mul
    (GaussianJet.listProd (gs.map (fun g => g.eval u (Fin.snoc a i)))))

@[simp] theorem symbolicIBPBranchJet_apply {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1))
    (ds : List (Fin e)) (gs : List (SymbolicGaussianFactor (e+1))) (x : Fin (n+1) → ℝ) :
    (symbolicIBPBranchJet u a ds gs).f x=
      ∑ i,((u i).iteratedPartial (ds.map a)).f x*symbolicProductValue u (Fin.snoc a i) gs x := by
  simp [symbolicIBPBranchJet,GaussianJet.finsetSum,GaussianJet.mul,GaussianJet.listProd_apply,
    symbolicProductValue,List.map_map,Function.comp_def]

private theorem finite_list_sum_swap {I A : Type*} [Fintype I]
    (bs : List A) (a : I → ℝ) (f : A → I → ℝ) :
    (∑ i,a i*(bs.map (fun b => f b i)).sum)=(bs.map (fun b => ∑ i,a i*f b i)).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih => simp [mul_add,Finset.sum_add_distrib,ih]

/-- Exact one-step expansion, including the new contracted Gaussian
coordinate. All functions are constructed jets, so every integral exists. -/
theorem symbolic_ibp_step {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1))
    (ds : List (Fin e)) (fs : List (SymbolicGaussianFactor e)) :
    (∫ x : Fin (n+1) → ℝ,symbolicProductValue u a fs x*
      ((SymbolicGaussianFactor.divergence ds).eval u a).f x
      ∂Measure.pi fun _ => gaussianReal 0 1)=
    ((symbolicProductBranches fs).map (fun gs =>
      ∫ x,(symbolicIBPBranchJet u a ds gs).f x ∂Measure.pi fun _ => gaussianReal 0 1)).sum := by
  let F := GaussianJet.listProd (fs.map (fun f => f.eval u a))
  let U := fun i => (u i).iteratedPartial (ds.map a)
  have hh := finite_gaussian_divergence_duality F.f
    (fun i => (F.partial i).f) (fun i => (U i).f) (fun i => ((U i).partial i).f)
    F.coordinate_derivative (fun i => (U i).coordinate_derivative i)
    F.smooth.continuous.measurable F.polynomial_growth
    (fun i => (F.partial i).smooth.continuous.measurable) (fun i => (F.partial i).polynomial_growth)
    (fun i => (U i).smooth.continuous.measurable) (fun i => (U i).polynomial_growth)
    (fun i => ((U i).partial i).smooth.continuous.measurable)
    (fun i => ((U i).partial i).polynomial_growth)
  have heF (x) : F.f x=symbolicProductValue u a fs x := by
    simp [F,GaussianJet.listProd_apply,symbolicProductValue,List.map_map,Function.comp_def]
  have heU (x) : ((SymbolicGaussianFactor.divergence ds).eval u a).f x=
      ∑ i,(x i*(U i).f x-((U i).partial i).f x) := GaussianJet.divergence_apply U x
  simp_rw [heF,← heU] at hh
  rw [← hh]
  have hi := GaussianJet.integral_listSum
    ((symbolicProductBranches fs).map (symbolicIBPBranchJet u a ds))
  simp only [List.map_map,Function.comp_def] at hi
  rw [← hi]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change (∑ i,(U i).f x*(F.partial i).f x)=_
  simp_rw [show ∀ i,(F.partial i).f x=
    ((symbolicProductBranches fs).map (fun gs => symbolicProductValue u (Fin.snoc a i) gs x)).sum from
      fun i => symbolic_product_branch_identity u a i fs x]
  rw [finite_list_sum_swap]
  simp only [GaussianJet.listSum_apply,List.map_map,Function.comp_def,symbolicIBPBranchJet_apply,U]

end Asakura.Chapter12
