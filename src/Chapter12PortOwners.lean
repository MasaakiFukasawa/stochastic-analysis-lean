import Chapter12ContractionGraphInvariant

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem port_owner_pair {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ports : V → Multiset E) (hn : ∀ v,(ports v).Nodup) (k : E)
    (hc : (∑ v,(ports v).count k)=2) :
    ∃ p q : V,p≠q ∧ ∀ v,k∈ports v ↔ v=p ∨ v=q := by
  let s := Finset.univ.filter (fun v => k∈ports v)
  have hs : s.card=2 := by
    rw [Finset.card_filter]
    simpa only [Multiset.count_eq_of_nodup (hn _)] using hc
  obtain ⟨p,q,hpq,he⟩ := Finset.card_eq_two.mp hs
  refine ⟨p,q,hpq,fun v => ?_⟩
  have hh : k∈ports v ↔ v∈s := by simp [s]
  rw [hh,he]
  simp

theorem contraction_ports_count_sum {e : ℕ} (fs : List (SymbolicGaussianFactor e)) (k : Fin e) :
    (∑ v : Fin fs.length,((fs.get v).ports).count k)=(contractionPorts fs).count k := by
  induction fs with
  | nil => simp [contractionPorts]
  | cons f fs ih =>
    simp only [List.length_cons] at *
    rw [Fin.sum_univ_succ]
    simpa [contractionPorts] using congrArg (fun a => f.ports.count k+a) ih

theorem contraction_ports_card_sum {e : ℕ} (fs : List (SymbolicGaussianFactor e)) :
    (∑ v : Fin fs.length,((fs.get v).ports).card)=(contractionPorts fs).card := by
  induction fs with
  | nil => simp [contractionPorts]
  | cons f fs ih =>
    simp only [List.length_cons] at *
    rw [Fin.sum_univ_succ]
    simpa [contractionPorts] using congrArg (fun a => f.ports.card+a) ih

theorem valid_contraction_endpoints (t : SymbolicIBPTerm) (ht : t.ValidContraction) :
    ∃ left right : Fin t.edges → Fin t.factors.length,
      (∀ k,left k≠right k) ∧
      ∀ k v,k∈(t.factors.get v).ports ↔ v=left k ∨ v=right k := by
  classical
  have h (k : Fin t.edges) := port_owner_pair (fun v : Fin t.factors.length => (t.factors.get v).ports)
    (fun v => ht.2 _ (List.get_mem _ _)) k
    (by rw [contraction_ports_count_sum];exact ht.1 k)
  choose left right hneq hmem using h
  exact ⟨left,right,hneq,hmem⟩

end Asakura.Chapter12
