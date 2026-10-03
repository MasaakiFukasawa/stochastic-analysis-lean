import Chapter12SymbolicIBPStep
import Chapter12SymbolicBranchProfiles

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable def symbolicTermMoment {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (fs : List (SymbolicGaussianFactor e)) : ℝ :=
  ∑ a : Fin e → Fin (n+1),∫ x,symbolicProductValue u a fs x ∂Measure.pi fun _ => gaussianReal 0 1

def symbolicIBPChildren {e : ℕ} (ds : List (Fin e)) (fs : List (SymbolicGaussianFactor e)) :
    List (List (SymbolicGaussianFactor (e+1))) :=
  (symbolicProductBranches fs).map (fun gs =>
    SymbolicGaussianFactor.plain (ds.map Fin.castSucc) (Fin.last e)::gs)

private theorem sum_snoc_assignments {e n : ℕ} (f : (Fin (e+1) → Fin (n+1)) → ℝ) :
    (∑ b,f b)=∑ a : Fin e → Fin (n+1),∑ i : Fin (n+1),f (Fin.snoc a i) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (e+1) => Fin (n+1))) f,
    Fintype.sum_prod_type,Finset.sum_comm]
  rfl

theorem symbolic_child_moment {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (ds : List (Fin e))
    (gs : List (SymbolicGaussianFactor (e+1))) :
    symbolicTermMoment u (SymbolicGaussianFactor.plain (ds.map Fin.castSucc) (Fin.last e)::gs)=
      ∑ a : Fin e → Fin (n+1),∫ x,(symbolicIBPBranchJet u a ds gs).f x
        ∂Measure.pi fun _ => gaussianReal 0 1 := by
  unfold symbolicTermMoment
  rw [sum_snoc_assignments]
  apply Finset.sum_congr rfl
  intro a _
  have hi (i : Fin (n+1)) := (((u i).iteratedPartial (ds.map a)).mul
    (GaussianJet.listProd (gs.map (fun g => g.eval u (Fin.snoc a i))))).integrable
  have he (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
      symbolicProductValue u (Fin.snoc a i)
        (SymbolicGaussianFactor.plain (ds.map Fin.castSucc) (Fin.last e)::gs) x=
      (((u i).iteratedPartial (ds.map a)).mul
        (GaussianJet.listProd (gs.map (fun g => g.eval u (Fin.snoc a i))))).f x := by
    simp [symbolicProductValue,SymbolicGaussianFactor.eval,GaussianJet.mul,
      GaussianJet.listProd_apply,List.map_map,Function.comp_def]
  simp_rw [he]
  rw [← integral_finset_sum _ (fun i _ => hi i)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp [symbolicIBPBranchJet,GaussianJet.finsetSum]

private theorem sum_list_sum_swap {I A : Type*} [Fintype I] (l : List A) (f : I → A → ℝ) :
    (∑ i,(l.map (f i)).sum)=(l.map (fun a => ∑ i,f i a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib,ih]

/-- The whole contracted expectation equals the sum over the next
branches; the new tensor index is summed internally and does not enlarge
the branch-count constant by the Gaussian dimension. -/
theorem symbolic_term_ibp_expansion {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (ds : List (Fin e))
    (fs : List (SymbolicGaussianFactor e)) :
    symbolicTermMoment u (SymbolicGaussianFactor.divergence ds::fs)=
      ((symbolicIBPChildren ds fs).map (symbolicTermMoment u)).sum := by
  unfold symbolicTermMoment
  simp only [symbolicProductValue_cons]
  have he (a : Fin e → Fin (n+1)) :
      (∫ x,((SymbolicGaussianFactor.divergence ds).eval u a).f x*symbolicProductValue u a fs x
        ∂Measure.pi fun _ => gaussianReal 0 1)=
      ((symbolicProductBranches fs).map (fun gs =>
        ∫ x,(symbolicIBPBranchJet u a ds gs).f x ∂Measure.pi fun _ => gaussianReal 0 1)).sum := by
    simpa only [mul_comm] using symbolic_ibp_step u a ds fs
  simp_rw [he]
  rw [sum_list_sum_swap]
  change _=((symbolicIBPChildren ds fs).map (symbolicTermMoment u)).sum
  simp only [symbolicIBPChildren,List.map_map,Function.comp_def,symbolic_child_moment]

end Asakura.Chapter12
