import Chapter8QuadraticComparison

namespace Asakura.Chapter8
noncomputable section

def newtonEnergy (δ b q v : ℝ) : ℝ := (b + δ^2/2)*q^2 + δ*q*v + v^2
def newtonDissipation (δ b h q v : ℝ) : ℝ := δ*h*q^2 + 2*(h-b)*q*v + δ*v^2

/-- One rate works for the full Hessian interval, not just its endpoints. -/
theorem newton_uniform_form_rate (l u δ : ℝ) (hl : 0 < l)
    (hlu : l ≤ u) (hδ : Real.sqrt u - Real.sqrt l < δ) :
    ∃ b r : ℝ, 0 < r ∧
      (∀ q v, q ≠ 0 ∨ v ≠ 0 → 0 < newtonEnergy δ b q v) ∧
      ∀ h, l ≤ h → h ≤ u → ∀ q v,
        2*r*newtonEnergy δ b q v ≤ newtonDissipation δ b h q v := by
  have hd : 0 < δ := lt_of_le_of_lt (sub_nonneg.mpr (Real.sqrt_le_sqrt hlu)) hδ
  obtain ⟨b,hb,hb'⟩ := newton_threshold_interval l u δ hl hlu hδ
  obtain ⟨hp,hlR,huR⟩ := newton_threshold_determinants l u δ b hl hlu hd hb hb'
  let P : ℝ × ℝ → ℝ := fun z => newtonEnergy δ b z.1 z.2
  let R : ℝ → ℝ × ℝ → ℝ := fun h z => newtonDissipation δ b h z.1 z.2
  have hz (z : ℝ × ℝ) (h : z ≠ 0) : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
    by_contra he
    push_neg at he
    exact h (Prod.ext he.1 he.2)
  have hP : Continuous P := by dsimp [P,newtonEnergy]; fun_prop
  have hR (h : ℝ) : Continuous (R h) := by dsimp [R,newtonDissipation]; fun_prop
  have hPs (a : ℝ) (z : ℝ × ℝ) : P (a • z) = a^2 * P z := by
    simp [P,newtonEnergy,Prod.smul_mk,smul_eq_mul]; ring
  have hRs (h a : ℝ) (z : ℝ × ℝ) : R h (a • z) = a^2 * R h z := by
    simp [R,newtonDissipation,Prod.smul_mk,smul_eq_mul]; ring
  have hpos (z : ℝ × ℝ) (h : z ≠ 0) : 0 < P z :=
    newton_energy_positive δ b z.1 z.2 hp (hz z h)
  obtain ⟨cl,hcl,hclR⟩ := positive_quadratic_comparison P (R l) hP (hR l) hpos
    (fun z h => newton_dissipation_positive δ l b z.1 z.2 hd hlR (hz z h)) hPs (hRs l)
  obtain ⟨cu,hcu,hcuR⟩ := positive_quadratic_comparison P (R u) hP (hR u) hpos
    (fun z h => newton_dissipation_positive δ u b z.1 z.2 hd huR (hz z h)) hPs (hRs u)
  refine ⟨b,min cl cu / 2, by positivity, ?_, ?_⟩
  · exact fun q v h => newton_energy_positive δ b q v hp h
  intro h hhl hhu q v
  have hpnon : 0 ≤ P (q,v) := by
    by_cases hh : (q,v) = (0:ℝ × ℝ)
    · simp only [Prod.mk_eq_zero] at hh
      simp [P,newtonEnergy,hh.1,hh.2]
    · exact (hpos _ hh).le
  have hll : min cl cu * P (q,v) ≤ R l (q,v) :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hpnon).trans (hclR _)
  have huu : min cl cu * P (q,v) ≤ R u (q,v) :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hpnon).trans (hcuR _)
  dsimp [P,R,newtonEnergy,newtonDissipation] at hll huu ⊢
  by_cases he : l = u
  · have hh : h = l := by linarith
    rw [hh]
    convert hll using 1 <;> ring
  · have hposul : 0 < u-l := by exact sub_pos.mpr (lt_of_le_of_ne hlu he)
    have ha := mul_nonneg (sub_nonneg.mpr hhu) (sub_nonneg.mpr hll)
    have hb := mul_nonneg (sub_nonneg.mpr hhl) (sub_nonneg.mpr huu)
    have hex : (u-h)*(δ*l*q^2+2*(l-b)*q*v+δ*v^2 - min cl cu*((b+δ^2/2)*q^2+δ*q*v+v^2)) +
        (h-l)*(δ*u*q^2+2*(u-b)*q*v+δ*v^2 - min cl cu*((b+δ^2/2)*q^2+δ*q*v+v^2)) =
        (u-l)*(δ*h*q^2+2*(h-b)*q*v+δ*v^2 - min cl cu*((b+δ^2/2)*q^2+δ*q*v+v^2)) := by ring
    have hh : 0 ≤ (u-l)*(δ*h*q^2+2*(h-b)*q*v+δ*v^2 - min cl cu*((b+δ^2/2)*q^2+δ*q*v+v^2)) := by
      rw [← hex]; exact add_nonneg ha hb
    have hh' := (mul_nonneg_iff_of_pos_left hposul).mp hh
    nlinarith only [hh']

end
end Asakura.Chapter8
