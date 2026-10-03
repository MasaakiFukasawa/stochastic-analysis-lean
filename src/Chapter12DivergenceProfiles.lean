import Chapter12HigherChainPartitions

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Orders and divergence flags of the actual n factors in an iterated
Gaussian IBP term. The tensor indices are handled separately. -/
inductive IBPFactor
  | plain : ℕ → IBPFactor
  | divergence : ℕ → IBPFactor
  deriving DecidableEq

def IBPFactor.order : IBPFactor → ℕ
  | .plain a => a
  | .divergence a => a

def IBPFactor.pending : IBPFactor → ℕ
  | .plain _ => 0
  | .divergence _ => 1

def ibpOrders (s : Multiset IBPFactor) : ℕ := (s.map IBPFactor.order).sum
def ibpPending (s : Multiset IBPFactor) : ℕ := (s.map IBPFactor.pending).sum

/-- The three branches in the manuscript. The first selected divergence
is removed; differentiating another divergence has two commutator branches. -/
inductive IBPProfileStep : Multiset IBPFactor → Multiset IBPFactor → Prop
  | plain (a b : ℕ) (s : Multiset IBPFactor) :
      IBPProfileStep (.divergence b ::ₘ .plain a ::ₘ s) (.plain b ::ₘ .plain (a+1) ::ₘ s)
  | correction (a b : ℕ) (s : Multiset IBPFactor) :
      IBPProfileStep (.divergence b ::ₘ .divergence a ::ₘ s) (.plain b ::ₘ .plain a ::ₘ s)
  | commute (a b : ℕ) (s : Multiset IBPFactor) :
      IBPProfileStep (.divergence b ::ₘ .divergence a ::ₘ s) (.plain b ::ₘ .divergence (a+1) ::ₘ s)

theorem ibp_profile_step_bounds {s t : Multiset IBPFactor} (h : IBPProfileStep s t) :
    t.card=s.card ∧ ibpPending t < ibpPending s ∧
      ibpOrders t+ibpPending t ≤ ibpOrders s+ibpPending s := by
  cases h <;> simp [ibpOrders,ibpPending,IBPFactor.order,IBPFactor.pending] <;> omega

/-- The number of pending divergences is a strict natural-number rank;
therefore no infinite IBP branch is possible. -/
theorem ibp_profile_wellFounded : WellFounded (fun t s => IBPProfileStep s t) :=
  Subrelation.wf (fun {_ _} h => (ibp_profile_step_bounds h).2.1)
    (measure ibpPending).wf

/-- Every term reachable from n copies of delta(u) retains exactly n
factors and has total derivative order plus remaining divergences at most n. -/
theorem ibp_profile_reachable (n : ℕ) (t : Multiset IBPFactor)
    (h : Relation.ReflTransGen IBPProfileStep (Multiset.replicate n (.divergence 0)) t) :
    t.card=n ∧ ibpOrders t+ibpPending t≤n := by
  induction h with
  | refl => simp [ibpOrders,ibpPending,IBPFactor.order,IBPFactor.pending]
  | @tail b c hbc hstep ih =>
    have hs := ibp_profile_step_bounds hstep
    exact ⟨hs.1.trans ih.1,hs.2.2.trans ih.2⟩

theorem ibp_profile_each_order (n : ℕ) (t : Multiset IBPFactor)
    (h : Relation.ReflTransGen IBPProfileStep (Multiset.replicate n (.divergence 0)) t)
    (f : IBPFactor) (hf : f∈t) : f.order≤n := by
  have hs : f.order ≤ ibpOrders t := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) f.order (Multiset.mem_map.mpr ⟨f,hf,rfl⟩)
  have hb := (ibp_profile_reachable n t h).2
  omega

end Asakura.Chapter12
