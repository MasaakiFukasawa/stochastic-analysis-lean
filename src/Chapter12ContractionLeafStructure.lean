import Chapter12ContractionGraphInvariant

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem factor_ports_order_identity {e : ℕ} (f : SymbolicGaussianFactor e) :
    f.ports.card+f.profile.pending=f.profile.order+1 := by
  cases f <;> simp [SymbolicGaussianFactor.ports,SymbolicGaussianFactor.profile,IBPFactor.pending,IBPFactor.order]

theorem total_ports_order_identity {e : ℕ} (fs : List (SymbolicGaussianFactor e)) :
    (contractionPorts fs).card+ibpPending (symbolicProfiles fs)=
      ibpOrders (symbolicProfiles fs)+fs.length := by
  induction fs with
  | nil => simp [contractionPorts,symbolicProfiles,ibpPending,ibpOrders]
  | cons f fs ih =>
    have hf := factor_ports_order_identity f
    simp only [contractionPorts,symbolicProfiles,Multiset.card_add,List.length_cons,
      ibpPending,ibpOrders,Multiset.map_cons,Multiset.sum_cons] at *
    omega

theorem valid_contraction_port_count (t : SymbolicIBPTerm) (ht : t.ValidContraction) :
    (contractionPorts t.factors).card=2*t.edges := by
  have hh := Multiset.sum_count_eq_card (s := Finset.univ) (m := contractionPorts t.factors)
    (fun a _ => Finset.mem_univ a)
  simpa only [ht.1,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_comm] using hh.symm

theorem terminal_contraction_edges (t : SymbolicIBPTerm) (ht : t.ValidContraction)
    (hterm : t.pending=0) (m : ℕ) (hsize : t.size=m) (hbudget : t.budget≤m) :
    t.edges≤m := by
  have hp := total_ports_order_identity t.factors
  rw [valid_contraction_port_count t ht] at hp
  change 2*t.edges+t.pending=ibpOrders (symbolicProfiles t.factors)+t.size at hp
  change ibpOrders (symbolicProfiles t.factors)+t.pending≤m at hbudget
  omega

/-- The leaves of the actual moment expansion are legitimate tensor
contractions: every index occurs twice, never twice in the same factor. -/
theorem divergence_moment_valid_expansion {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (m : ℕ) (hm : 2≤m) :
    ∃ C : IBPExpansion,C.value=(divergenceMomentRoot m).moment u ∧
      C.leafCount≤(2*(m-1))^m ∧
      C.LeavesSatisfy (fun v => ∃ s : SymbolicIBPTerm,
        s.ValidContraction ∧ s.pending=0 ∧ s.size=m ∧ s.budget≤m ∧ s.edges≤m ∧ v=s.moment u) := by
  obtain ⟨C,hv,hcount,hl⟩ := divergence_moment_finite_expansion u m hm
  refine ⟨C,by simpa only [divergence_root_moment] using hv,hcount,?_⟩
  apply C.leavesSatisfy_mono hl
  intro v hv
  obtain ⟨s,hs0,hss,hsb,hsv,hpath⟩ := hv
  have hvalid := reachable_valid_contraction hpath (divergence_root_valid_contraction m)
  exact ⟨s,hvalid,hs0,hss,hsb,terminal_contraction_edges s hvalid hs0 m hss hsb,hsv⟩

end Asakura.Chapter12
