import Chapter12PortOwners
import Chapter12FiniteTensorNetwork
import Chapter12ContractionLeafStructure

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def SymbolicGaussianFactor.portList {e : ℕ} : SymbolicGaussianFactor e → List (Fin e)
  | .plain ds i => i::ds
  | .divergence ds => ds

@[simp] theorem SymbolicGaussianFactor.portList_coe {e : ℕ} (f : SymbolicGaussianFactor e) :
    (f.portList : Multiset (Fin e))=f.ports := by cases f <;> rfl

noncomputable def SymbolicGaussianFactor.coordinateArray {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (x : Fin (n+1) → ℝ) :
    (f : SymbolicGaussianFactor e) → (Fin f.portList.length → Fin (n+1)) → ℝ
  | .plain ds _,b => ((u (b ⟨0,by simp [SymbolicGaussianFactor.portList]⟩)).iteratedPartial (List.ofFn (fun j : Fin ds.length => b j.succ))).f x
  | .divergence ds,b => (GaussianJet.divergence (fun j => (u j).iteratedPartial (List.ofFn b))).f x

@[simp] theorem factor_array_eval {e n : ℕ} (f : SymbolicGaussianFactor e)
    (u : Fin (n+1) → GaussianJet (n+1)) (x : Fin (n+1) → ℝ) (a : Fin e → Fin (n+1)) :
    f.coordinateArray u x (a ∘ f.portList.get)=(f.eval u a).f x := by
  cases f with
  | plain ds i =>
    simp only [SymbolicGaussianFactor.coordinateArray,SymbolicGaussianFactor.portList,
      Function.comp_apply,List.get_cons_zero,List.get_cons_succ,SymbolicGaussianFactor.eval]
    change ((u (a i)).iteratedPartial (List.ofFn (a ∘ ds.get))).f x=_
    rw [← List.map_ofFn,List.ofFn_get]
  | divergence ds =>
    simp only [SymbolicGaussianFactor.coordinateArray,SymbolicGaussianFactor.portList,
      Function.comp_apply,SymbolicGaussianFactor.eval]
    simp only [← List.map_ofFn,List.ofFn_get]

theorem valid_factor_port_injective (t : SymbolicIBPTerm) (ht : t.ValidContraction)
    (v : Fin t.factors.length) : Function.Injective (t.factors.get v).portList.get := by
  apply List.nodup_iff_injective_get.mp
  have hh := ht.2 (t.factors.get v) (List.get_mem _ _)
  simpa only [← SymbolicGaussianFactor.portList_coe,Multiset.coe_nodup] using hh

theorem valid_factor_degrees (t : SymbolicIBPTerm) (ht : t.ValidContraction) :
    (∑ v : Fin t.factors.length,(t.factors.get v).portList.length)=2*t.edges := by
  have hh := (contraction_ports_card_sum t.factors).trans (valid_contraction_port_count t ht)
  simpa only [← SymbolicGaussianFactor.portList_coe,Multiset.coe_card] using hh

/-- Pointwise bound on the very contractions produced by Gaussian integration
by parts, before integrating over the Gaussian variable. -/
theorem symbolic_contraction_pointwise_bound {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (t : SymbolicIBPTerm) (ht : t.ValidContraction)
    (x : Fin (n+1) → ℝ) :
    |∑ a : Fin t.edges → Fin (n+1),symbolicProductValue u a t.factors x|≤
      ∏ v : Fin t.factors.length,Real.sqrt
        (∑ b : Fin (t.factors.get v).portList.length → Fin (n+1),
          (t.factors.get v).coordinateArray u x b ^ 2) := by
  classical
  obtain ⟨left,right,hneq,hmem⟩ := valid_contraction_endpoints t ht
  have hcover : ∀ v k,v≠left k → v≠right k →
      ∀ j,(t.factors.get v).portList.get j≠k := by
    intro v k hvl hvr j he
    have hk : k∈(t.factors.get v).ports := by
      rw [← SymbolicGaussianFactor.portList_coe]
      exact he ▸ List.get_mem _ j
    exact ((hmem k v).mp hk).elim hvl hvr
  have hh := finite_tensor_network_bound n t.edges
    (fun v : Fin t.factors.length => (t.factors.get v).portList.length)
    (fun v => (t.factors.get v).portList.get) (valid_factor_port_injective t ht)
    left right hneq hcover (valid_factor_degrees t ht)
    (fun v => (t.factors.get v).coordinateArray u x)
  simp only [factor_array_eval] at hh
  convert hh using 1
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change (t.factors.map (fun f => (f.eval u a).f x)).prod=_
  change (t.factors.map (fun f => (f.eval u a).f x)).prod=
    ∏ v : Fin t.factors.length,(t.factors.get v |>.eval u a).f x
  conv_lhs => rw [← List.ofFn_get t.factors,List.map_ofFn,List.prod_ofFn]
  rfl

end Asakura.Chapter12
