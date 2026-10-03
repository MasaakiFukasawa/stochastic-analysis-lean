import Chapter12LpInclusion

open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem even_exponent_dominates (r : ℝ≥0∞) (hr : r≠⊤) :
    ∃ p : ℕ,0<p ∧ r≤(2*p:ℕ) ∧ (2:ℝ≥0∞)≤(2*p:ℕ) := by
  obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hr
  refine ⟨n+1,by omega,?_,?_⟩
  · exact hn.le.trans (by exact_mod_cast (show n≤2*(n+1) by omega))
  · exact_mod_cast (show 2≤2*(n+1) by omega)

theorem even_conjugate_properties (p : ℕ) (hp : 0<p) :
    1≤ENNReal.conjExponent (2*p:ℕ) ∧ ENNReal.conjExponent (2*p:ℕ)≠⊤ := by
  have hm : (1:ℝ≥0∞)<(2*p:ℕ) := by exact_mod_cast (show 1<2*p by omega)
  constructor
  · unfold ENNReal.conjExponent
    exact le_self_add
  · unfold ENNReal.conjExponent
    exact ENNReal.add_ne_top.mpr ⟨by simp,ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hm).ne'⟩

end Asakura.Chapter12
