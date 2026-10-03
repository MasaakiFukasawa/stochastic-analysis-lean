import Chapter12CylinderJetSizeMonotone

namespace Asakura.Chapter12

theorem finite_prefix_member_le (f:ℕ → ℝ) (hf:∀i,0≤f i) {j k:ℕ} (hjk:j≤k) :
    f j≤∑i:Fin (k+1),f i.val := by
  exact Finset.single_le_sum (fun i _ => hf i.val) (Finset.mem_univ (⟨j,by omega⟩:Fin (k+1)))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.finite_prefix_member_le
