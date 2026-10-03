import Chapter12ProductPortInvariant
import Chapter12DivergenceMomentExpansion

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

def SymbolicIBPTerm.ValidContraction (t : SymbolicIBPTerm) : Prop :=
  (∀ i : Fin t.edges,(contractionPorts t.factors).count i=2) ∧
    ∀ f∈t.factors,f.ports.Nodup

theorem fresh_pair_counts {e : ℕ} (s : Multiset (Fin e)) (hs : ∀ i,s.count i=2) :
    ∀ i : Fin (e+1),(Fin.last e::ₘFin.last e::ₘs.map Fin.castSucc).count i=2 := by
  intro j
  have hnew : Fin.last e∉s.map Fin.castSucc := by
    intro h
    obtain ⟨i,hi,he⟩ := Multiset.mem_map.mp h
    exact Fin.castSucc_ne_last i he
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [Multiset.count_eq_zero.mpr hnew]
  · have hc := Multiset.count_map_eq_count' Fin.castSucc s (Fin.castSucc_injective e) i
    simpa [Fin.castSucc_ne_last,Ne.symm (Fin.castSucc_ne_last i),hc] using hs i

/-- Every created edge joins two different original factors; therefore
all indices remain paired and no self-contraction is introduced. -/
theorem symbolic_successor_valid_contraction {t c : SymbolicIBPTerm}
    (h : t.Successor c) (ht : t.ValidContraction) : c.ValidContraction := by
  obtain ⟨ds,fs,gs,hperm,hgs,rfl⟩ := h
  have hcounts : ∀ i,(contractionPorts (SymbolicGaussianFactor.divergence ds::fs)).count i=2 := by
    rw [← contraction_ports_perm hperm]
    exact ht.1
  have hnodup : ∀ f∈SymbolicGaussianFactor.divergence ds::fs,f.ports.Nodup :=
    fun f hf => ht.2 f (hperm.mem_iff.mpr hf)
  obtain ⟨hs,hhs,rfl⟩ := List.mem_map.mp hgs
  have hp := symbolic_product_port_invariant fs
    (fun f hf => hnodup f (List.mem_cons_of_mem _ hf)) hs hhs
  have he : contractionPorts (SymbolicGaussianFactor.plain (ds.map Fin.castSucc) (Fin.last t.edges)::hs)=
      Fin.last t.edges::ₘFin.last t.edges::ₘ
        ((contractionPorts (SymbolicGaussianFactor.divergence ds::fs)).map Fin.castSucc) := by
    simp [contractionPorts,SymbolicGaussianFactor.ports,hp.1,← Multiset.singleton_add,
      add_comm,add_left_comm,add_assoc]
  constructor
  · change ∀ i,(contractionPorts _).count i=2
    rw [he]
    exact fresh_pair_counts _ hcounts
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · have hh := hnodup (.divergence ds) (List.mem_cons_self)
      change (ds : Multiset (Fin t.edges)).Nodup at hh
      simpa [SymbolicGaussianFactor.ports] using fresh_endpoint_nodup (ds : Multiset (Fin t.edges)) hh
    · exact hp.2 f hf

theorem divergence_root_valid_contraction (m : ℕ) : (divergenceMomentRoot m).ValidContraction := by
  constructor
  · intro i
    exact Fin.elim0 i
  · intro f hf
    have he : f=SymbolicGaussianFactor.divergence [] := (List.mem_replicate.mp hf).2
    subst f
    simp [SymbolicGaussianFactor.ports]

theorem reachable_valid_contraction {t c : SymbolicIBPTerm}
    (h : Relation.ReflTransGen SymbolicIBPTerm.Successor t c) (ht : t.ValidContraction) :
    c.ValidContraction := by
  induction h with
  | refl => exact ht
  | tail h hs ih => exact symbolic_successor_valid_contraction hs ih

end Asakura.Chapter12
