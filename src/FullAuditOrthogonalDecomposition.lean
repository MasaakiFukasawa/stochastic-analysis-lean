import ManuscriptProjection

open Set
open scoped InnerProductSpace Topology
namespace Asakura.FullAudit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The subspace C-perp as explicitly defined in the appendix. -/
def writtenPerp (C : Submodule ℝ H) : Submodule ℝ H where
  carrier := {h | ∀ g ∈ C, inner ℝ h g = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy g hg
    simp [inner_add_left, hx g hg, hy g hg]
  smul_mem' := by
    intro a x hx g hg
    simp [inner_smul_left, hx g hg]

/-- Its closedness follows by intersecting kernels of continuous inner products. -/
theorem writtenPerp_closed (C : Submodule ℝ H) : IsClosed (writtenPerp C : Set H) := by
  have heq : (writtenPerp C : Set H) = ⋂ g : C, {h : H | inner ℝ h (g : H) = 0} := by
    ext h
    simp [writtenPerp]
  rw [heq]
  apply isClosed_iInter
  intro g
  exact isClosed_eq (continuous_id.inner continuous_const) continuous_const

/-- The zero intersection is proved with the squared norm, as printed. -/
theorem writtenPerp_inter_zero (C : Submodule ℝ H) (u : H)
    (hu : u ∈ C) (hp : u ∈ writtenPerp C) : u = 0 := by
  have hself := hp u hu
  exact inner_self_eq_zero.mp hself

/-- Construct and identify the two components using the already checked projection proof. -/
theorem orthogonal_decomposition_written [CompleteSpace H]
    (C : Submodule ℝ H) (hC : IsClosed (C : Set H)) (f : H) :
    ∃! z : H × H, z.1 ∈ C ∧ z.2 ∈ writtenPerp C ∧ f = z.1+z.2 := by
  obtain ⟨g, hg, hmin⟩ := Asakura.manuscript_projection_exists (C : Set H)
    C.nonempty hC C.convex f
  have hh : f-g ∈ writtenPerp C :=
    (Asakura.manuscript_projection_orthogonal C f g hg).mp hmin
  refine ⟨(g,f-g), ⟨hg,hh,by simp⟩, ?_⟩
  rintro ⟨g',h'⟩ ⟨hg',hh',heq⟩
  have hperp : g'-g ∈ writtenPerp C := by
    have he : g'-g = (f-g)-h' := by rw [heq]; abel
    rw [he]
    exact (writtenPerp C).sub_mem hh hh'
  have hzero := writtenPerp_inter_zero C (g'-g) (C.sub_mem hg' hg) hperp
  have he : g' = g := sub_eq_zero.mp hzero
  apply Prod.ext he
  dsimp
  rw [← he, heq]
  abel

/-- Pythagoras, including the projection bound. -/
theorem orthogonal_decomposition_norm (C : Submodule ℝ H) (g h : H)
    (hg : g ∈ C) (hh : h ∈ writtenPerp C) :
    ‖g+h‖^2 = ‖g‖^2+‖h‖^2 ∧ ‖g‖ ≤ ‖g+h‖ := by
  have horth : inner ℝ g h = 0 := by rw [real_inner_comm]; exact hh g hg
  have he : ‖g+h‖^2 = ‖g‖^2+‖h‖^2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  exact ⟨he, by nlinarith [sq_nonneg ‖h‖, norm_nonneg g, norm_nonneg (g+h)]⟩

/-- Uniqueness forces linearity; the norm identity gives continuity. -/
theorem orthogonal_projection_linear_continuous [CompleteSpace H]
    (C : Submodule ℝ H) (hC : IsClosed (C : Set H))
    (P : H → H) (hP : ∀ f, P f ∈ C ∧ f-P f ∈ writtenPerp C) :
    (∀ (a b : ℝ) (f g : H), P (a • f+b • g)=a • P f+b • P g) ∧
    (∀ f, ‖P f‖ ≤ ‖f‖) ∧ Continuous P := by
  have hlinear (a b : ℝ) (f g : H) : P (a • f+b • g)=a • P f+b • P g := by
    let k := a • P f+b • P g
    have hk : k ∈ C := C.add_mem (C.smul_mem a (hP f).1) (C.smul_mem b (hP g).1)
    have hr : (a • f+b • g)-k ∈ writtenPerp C := by
      have he : (a • f+b • g)-k = a • (f-P f)+b • (g-P g) := by dsimp [k]; module
      rw [he]
      exact (writtenPerp C).add_mem ((writtenPerp C).smul_mem a (hP f).2)
        ((writtenPerp C).smul_mem b (hP g).2)
    have he : P (a • f+b • g)-k = ((a • f+b • g)-k)-((a • f+b • g)-P (a • f+b • g)) := by abel
    apply sub_eq_zero.mp
    apply writtenPerp_inter_zero C _ (C.sub_mem (hP _).1 hk)
    rw [he]
    exact (writtenPerp C).sub_mem hr (hP _).2
  have hnorm (f : H) : ‖P f‖ ≤ ‖f‖ := by
    simpa using (orthogonal_decomposition_norm C (P f) (f-P f) (hP f).1 (hP f).2).2
  refine ⟨hlinear, hnorm, ?_⟩
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hsub : P (f-g)=P f-P g := by simpa [sub_eq_add_neg] using hlinear 1 (-1) f g
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, hsub] using hnorm (f-g)

end Asakura.FullAudit

#print axioms Asakura.FullAudit.writtenPerp_closed
#print axioms Asakura.FullAudit.writtenPerp_inter_zero
#print axioms Asakura.FullAudit.orthogonal_decomposition_written
#print axioms Asakura.FullAudit.orthogonal_decomposition_norm
#print axioms Asakura.FullAudit.orthogonal_projection_linear_continuous
