import Chapter12IBPBranchBound

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

def IBPExpansion.LeavesSatisfy (P : ℝ → Prop) : IBPExpansion → Prop
  | .leaf v => P v
  | .split _ children => ∀ j,(children j).LeavesSatisfy P

theorem IBPExpansion.leavesSatisfy_mono {P Q : ℝ → Prop} (C : IBPExpansion)
    (h : C.LeavesSatisfy P) (hPQ : ∀ v,P v → Q v) : C.LeavesSatisfy Q := by
  induction C with
  | leaf v => exact hPQ v h
  | split m children ih => exact fun j => ih j (h j)

theorem IBPExpansion.boundedBranches_mono (C : IBPExpansion) (B s r : ℕ)
    (h : C.BoundedBranches B s) (hsr : s≤r) : C.BoundedBranches B r := by
  induction C generalizing s r with
  | leaf _ => trivial
  | split m children ih =>
    obtain ⟨hs,hm,hc⟩ := h
    exact ⟨by omega,hm,fun j => ih j (s-1) (r-1) (hc j) (by omega)⟩

theorem IBPExpansion.leavesSatisfy_bound (C : IBPExpansion) (P : ℝ → Prop)
    (h : C.LeavesSatisfy P) (M : ℝ) (hb : ∀ v,P v → |v|≤M) : C.LeavesBounded M := by
  induction C with
  | leaf v => exact hb v h
  | split m children ih => exact fun j => ih j (h j)

end Asakura.Chapter12
