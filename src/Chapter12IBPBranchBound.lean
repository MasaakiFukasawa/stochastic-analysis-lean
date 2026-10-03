import Chapter12ReindexedContractions
import Chapter12DivergenceProfiles

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- A finite expansion keeps every summand; no cancellation is needed
for the dimension-independent moment bound. -/
inductive IBPExpansion
  | leaf (value : ℝ)
  | split (m : ℕ) (children : Fin m → IBPExpansion)

noncomputable def IBPExpansion.value : IBPExpansion → ℝ
  | .leaf v => v
  | .split _ children => ∑ j,(children j).value

def IBPExpansion.leafCount : IBPExpansion → ℕ
  | .leaf _ => 1
  | .split _ children => ∑ j,(children j).leafCount

def IBPExpansion.BoundedBranches (B r : ℕ) : IBPExpansion → Prop
  | .leaf _ => True
  | .split m children => 0<r ∧ m≤B ∧ ∀ j,(children j).BoundedBranches B (r-1)

def IBPExpansion.LeavesBounded (M : ℝ) : IBPExpansion → Prop
  | .leaf v => |v|≤M
  | .split _ children => ∀ j,(children j).LeavesBounded M

theorem ibp_expansion_leaf_count (C : IBPExpansion) (B r : ℕ) (hB : 1≤B)
    (h : C.BoundedBranches B r) : C.leafCount≤B^r := by
  induction C generalizing r with
  | leaf v => exact Nat.one_le_pow _ _ hB
  | split m children ih =>
    obtain ⟨hr,hm,hchildren⟩ := h
    change (∑ j,(children j).leafCount)≤B^r
    calc
      _ ≤ ∑ _ : Fin m,B^(r-1) := Finset.sum_le_sum (fun j _ => ih j (r-1) (hchildren j))
      _ = m*B^(r-1) := by simp
      _ ≤ B*B^(r-1) := Nat.mul_le_mul_right _ hm
      _ = B^r := by rw [← pow_succ'];congr 1;omega

theorem ibp_expansion_value_bound (C : IBPExpansion) (M : ℝ)
    (h : C.LeavesBounded M) : |C.value|≤C.leafCount*M := by
  induction C with
  | leaf v => simpa [IBPExpansion.value,IBPExpansion.leafCount,IBPExpansion.LeavesBounded] using h
  | split m children ih =>
    change |∑ j,(children j).value|≤(∑ j,(children j).leafCount : ℕ)*M
    calc
      _ ≤ ∑ j,|(children j).value| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j,((children j).leafCount:ℝ)*M := Finset.sum_le_sum (fun j _ => ih j (h j))
      _ = _ := by rw [← Finset.sum_mul,Nat.cast_sum]

theorem ibp_expansion_uniform_bound (C : IBPExpansion) (B r : ℕ) (hB : 1≤B)
    (h : C.BoundedBranches B r) (M : ℝ) (hM : 0≤M) (hleaf : C.LeavesBounded M) :
    |C.value|≤(B:ℝ)^r*M := by
  apply (ibp_expansion_value_bound C M hleaf).trans
  apply mul_le_mul_of_nonneg_right _ hM
  exact_mod_cast ibp_expansion_leaf_count C B r hB h

end Asakura.Chapter12
