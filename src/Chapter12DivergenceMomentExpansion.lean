import Chapter12SymbolicExpansionPaths

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

def divergenceMomentRoot (m : ℕ) : SymbolicIBPTerm :=
  ⟨0,List.replicate m (SymbolicGaussianFactor.divergence [])⟩

theorem divergence_root_profiles (m : ℕ) :
    symbolicProfiles (divergenceMomentRoot m).factors=Multiset.replicate m (.divergence 0) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simpa only [divergenceMomentRoot,List.replicate_succ,symbolicProfiles,
      SymbolicGaussianFactor.profile,List.length_nil,Multiset.replicate_succ] using
      congrArg (fun s => IBPFactor.divergence 0::ₘs) ih

@[simp] theorem divergence_root_pending (m : ℕ) : (divergenceMomentRoot m).pending=m := by
  simp [SymbolicIBPTerm.pending,divergence_root_profiles,ibpPending,IBPFactor.pending]

@[simp] theorem divergence_root_budget (m : ℕ) : (divergenceMomentRoot m).budget=m := by
  simp [SymbolicIBPTerm.budget,divergence_root_profiles,ibpOrders,IBPFactor.order]

@[simp] theorem divergence_root_size (m : ℕ) : (divergenceMomentRoot m).size=m := by
  simp [SymbolicIBPTerm.size,divergenceMomentRoot]

theorem divergence_root_moment {n : ℕ} (u : Fin (n+1) → GaussianJet (n+1)) (m : ℕ) :
    (divergenceMomentRoot m).moment u=
      ∫ x,(GaussianJet.divergence u).f x^m ∂Measure.pi fun _ => gaussianReal 0 1 := by
  simp [SymbolicIBPTerm.moment,symbolicTermMoment,divergenceMomentRoot,
    symbolicProductValue,SymbolicGaussianFactor.eval,GaussianJet.iteratedPartial]

/-- The n-factor moment expansion in the manuscript is finite, every
leaf is an actual fully differentiated contraction, and the number of
leaves is bounded independently of the number of Gaussian coordinates. -/
theorem divergence_moment_finite_expansion {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (m : ℕ) (hm : 2≤m) :
    ∃ C : IBPExpansion,
      C.value=(∫ x,(GaussianJet.divergence u).f x^m ∂Measure.pi fun _ => gaussianReal 0 1) ∧
      C.leafCount≤(2*(m-1))^m ∧
      C.LeavesSatisfy (fun v => ∃ s : SymbolicIBPTerm,
        s.pending=0 ∧ s.size=m ∧ s.budget≤m ∧ v=s.moment u ∧
          Relation.ReflTransGen SymbolicIBPTerm.Successor (divergenceMomentRoot m) s) := by
  obtain ⟨C,hv,hb,hl⟩ := symbolic_finite_ibp_expansion_paths u (divergenceMomentRoot m)
    (2*(m-1)) (by simp)
  refine ⟨C,?_,?_,?_⟩
  · simpa only [divergence_root_moment] using hv
  · have hh := ibp_expansion_leaf_count C (2*(m-1)) m (by omega) (by simpa only [divergence_root_pending] using hb)
    exact hh
  · simpa only [divergence_root_size,divergence_root_budget] using hl

end Asakura.Chapter12
