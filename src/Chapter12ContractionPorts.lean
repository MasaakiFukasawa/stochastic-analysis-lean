import Chapter12SymbolicSuccessors

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def SymbolicGaussianFactor.ports {e : ℕ} : SymbolicGaussianFactor e → Multiset (Fin e)
  | .plain ds out => out::ₘ(ds : Multiset (Fin e))
  | .divergence ds => (ds : Multiset (Fin e))

def contractionPorts {e : ℕ} : List (SymbolicGaussianFactor e) → Multiset (Fin e)
  | [] => 0
  | f::fs => f.ports+contractionPorts fs

@[simp] theorem factor_ports_reindex {e q : ℕ} (r : Fin e → Fin q) (f : SymbolicGaussianFactor e) :
    (f.reindex r).ports=f.ports.map r := by
  cases f <;> simp [SymbolicGaussianFactor.reindex,SymbolicGaussianFactor.ports]

@[simp] theorem contraction_ports_reindex {e q : ℕ} (r : Fin e → Fin q)
    (fs : List (SymbolicGaussianFactor e)) :
    contractionPorts (fs.map (SymbolicGaussianFactor.reindex r))=(contractionPorts fs).map r := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [contractionPorts,ih]

theorem contraction_ports_perm {e : ℕ} {fs gs : List (SymbolicGaussianFactor e)} (h : fs.Perm gs) :
    contractionPorts fs=contractionPorts gs := by
  induction h with
  | nil => rfl
  | cons f h ih => simp [contractionPorts,ih]
  | swap f g fs => simp [contractionPorts,add_comm,add_left_comm,add_assoc]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- Each differentiated factor receives exactly one fresh edge endpoint. -/
theorem derivative_branch_ports {e : ℕ} (f : SymbolicGaussianFactor e)
    (g : SymbolicGaussianFactor (e+1)) (hg : g∈f.derivativeBranches) :
    g.ports=Fin.last e::ₘ(f.ports.map Fin.castSucc) := by
  cases f with
  | plain ds out =>
    simp only [SymbolicGaussianFactor.derivativeBranches,List.mem_singleton] at hg
    subst g
    simp [SymbolicGaussianFactor.ports,← Multiset.cons_coe,← Multiset.singleton_add,add_comm,add_left_comm,add_assoc]
  | divergence ds =>
    simp only [SymbolicGaussianFactor.derivativeBranches,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl <;> simp [SymbolicGaussianFactor.ports]

theorem fresh_endpoint_nodup {e : ℕ} (s : Multiset (Fin e)) (hs : s.Nodup) :
    (Fin.last e::ₘ(s.map Fin.castSucc)).Nodup := by
  apply Multiset.nodup_cons.mpr
  constructor
  · intro h
    obtain ⟨i,hi,he⟩ := Multiset.mem_map.mp h
    exact Fin.castSucc_ne_last i he
  · exact hs.map (Fin.castSucc_injective e)

theorem derivative_branch_nodup {e : ℕ} (f : SymbolicGaussianFactor e)
    (hf : f.ports.Nodup) (g : SymbolicGaussianFactor (e+1)) (hg : g∈f.derivativeBranches) :
    g.ports.Nodup := by
  rw [derivative_branch_ports f g hg]
  exact fresh_endpoint_nodup f.ports hf

end Asakura.Chapter12
