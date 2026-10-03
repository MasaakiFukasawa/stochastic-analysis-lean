import Chapter12FactorCoordinateArrays
import Chapter12GaussianArrayNorm

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem symbolic_profile_mem {e : ℕ} (fs : List (SymbolicGaussianFactor e))
    (f : SymbolicGaussianFactor e) (hf : f∈fs) : f.profile∈symbolicProfiles fs := by
  induction fs with
  | nil => simp at hf
  | cons g gs ih =>
    rcases List.mem_cons.mp hf with rfl | hh
    · exact Multiset.mem_cons_self _ _
    · exact Multiset.mem_cons_of_mem (ih hh)

theorem terminal_factor_plain (t : SymbolicIBPTerm) (hterm : t.pending=0)
    (f : SymbolicGaussianFactor t.edges) (hf : f∈t.factors) :
    ∃ ds i,f=.plain ds i := by
  have hh : f.profile.pending≤t.pending :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _) f.profile.pending
      (Multiset.mem_map.mpr ⟨f.profile,symbolic_profile_mem t.factors f hf,rfl⟩)
  cases f with
  | plain ds i => exact ⟨ds,i,rfl⟩
  | divergence ds => simp [hterm,SymbolicGaussianFactor.profile,IBPFactor.pending] at hh

theorem factor_order_le_budget (t : SymbolicIBPTerm)
    (f : SymbolicGaussianFactor t.edges) (hf : f∈t.factors) : f.profile.order≤t.budget := by
  have hh : f.profile.order≤ ibpOrders (symbolicProfiles t.factors) :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _) f.profile.order
      (Multiset.mem_map.mpr ⟨f.profile,symbolic_profile_mem t.factors f hf,rfl⟩)
  exact hh.trans (Nat.le_add_right _ _)

theorem terminal_contraction_pointwise {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (t : SymbolicIBPTerm) (ht : t.ValidContraction)
    (hterm : t.pending=0) (m : ℕ) (hb : t.budget≤m) (x : Fin (n+1) → ℝ) :
    |∑ a : Fin t.edges → Fin (n+1),symbolicProductValue u a t.factors x|≤
      gaussianSobolevSum u m x ^ t.size := by
  apply (symbolic_contraction_pointwise_bound u t ht x).trans
  calc
    _ ≤ ∏ _ : Fin t.factors.length,gaussianSobolevSum u m x := by
      apply Finset.prod_le_prod₀ (fun _ _ => Real.sqrt_nonneg _)
      intro v _
      obtain ⟨ds,i,he⟩ := terminal_factor_plain t hterm (t.factors.get v) (List.get_mem _ _)
      have hk := (factor_order_le_budget t (t.factors.get v) (List.get_mem _ _)).trans hb
      rw [he] at hk ⊢
      change ds.length≤m at hk
      change gaussianDerivativeNorm u ds.length x≤gaussianSobolevSum u m x
      exact Finset.single_le_sum (f := fun k : Fin (m+1) => gaussianDerivativeNorm u k x) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ (⟨ds.length,by omega⟩ : Fin (m+1)))
    _ = _ := by simp [SymbolicIBPTerm.size]

theorem symbolic_product_integrable {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1))
    (fs : List (SymbolicGaussianFactor e)) :
    Integrable (symbolicProductValue u a fs) (Measure.pi fun _ => gaussianReal 0 1) := by
  have he : (GaussianJet.listProd (fs.map (fun f => f.eval u a))).f=symbolicProductValue u a fs := by
    funext x
    simp only [GaussianJet.listProd_apply,List.map_map,Function.comp_def,symbolicProductValue]
  rw [← he]
  exact (GaussianJet.listProd (fs.map (fun f => f.eval u a))).integrable

/-- The terminal expectation is bounded in actual Gaussian Lp, not by
an assumed bound on the leaves of a symbolic expansion. -/
theorem terminal_contraction_moment {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (t : SymbolicIBPTerm) (ht : t.ValidContraction)
    (hterm : t.pending=0) (m : ℕ) (hb : t.budget≤m) (hs : t.size=m) :
    |t.moment u|≤∫ x,gaussianSobolevSum u m x^m ∂Measure.pi fun _ => gaussianReal 0 1 := by
  have hi := integrable_finset_sum Finset.univ (fun a _ => symbolic_product_integrable u a t.factors)
  have he : t.moment u=∫ x,∑ a : Fin t.edges → Fin (n+1),symbolicProductValue u a t.factors x
      ∂Measure.pi fun _ => gaussianReal 0 1 := by
    exact (integral_finset_sum _ (fun a _ => symbolic_product_integrable u a t.factors)).symm
  rw [he]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono hi.abs (gaussianSobolevSum_power_integrable u m m)
  intro x
  simpa only [hs] using terminal_contraction_pointwise u t ht hterm m hb x

end Asakura.Chapter12
