import Chapter12TerminalContractionBound

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-- Dimension-free estimate obtained by the complete finite Gaussian IBP
expansion. The right side consists of actual coordinate derivative norms. -/
theorem actual_divergence_moment_bound {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (m : ℕ) (hm : 2≤m) :
    |∫ x,(GaussianJet.divergence u).f x^m ∂Measure.pi fun _ => gaussianReal 0 1|≤
      (2*(m-1):ℕ)^m *
      (∫ x,gaussianSobolevSum u m x^m ∂Measure.pi fun _ => gaussianReal 0 1) := by
  obtain ⟨C,hv,hcount,hleaves⟩ := divergence_moment_valid_expansion u m hm
  let M := ∫ x,gaussianSobolevSum u m x^m ∂Measure.pi fun _ => gaussianReal 0 1
  have hM : 0≤M := integral_nonneg (fun x => pow_nonneg (gaussianSobolevSum_nonneg u m x) m)
  have hbound : C.LeavesBounded M := by
    apply C.leavesSatisfy_bound _ hleaves M
    intro v hv
    obtain ⟨s,hvalid,hs0,hsize,hbudget,_,rfl⟩ := hv
    exact terminal_contraction_moment u s hvalid hs0 m hbudget hsize
  have hh := ibp_expansion_value_bound C M hbound
  rw [hv,divergence_root_moment] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hM)

/-- In the even case the left side is the genuine nonnegative moment. -/
theorem actual_divergence_even_moment {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (p : ℕ) (hp : 1≤p) :
    (∫ x,|(GaussianJet.divergence u).f x|^(2*p) ∂Measure.pi fun _ => gaussianReal 0 1)≤
      (2*(2*p-1):ℕ)^(2*p) *
      (∫ x,gaussianSobolevSum u (2*p) x^(2*p) ∂Measure.pi fun _ => gaussianReal 0 1) := by
  have hh := actual_divergence_moment_bound u (2*p) (by omega)
  have he : ∀ x,|(GaussianJet.divergence u).f x|^(2*p)=(GaussianJet.divergence u).f x^(2*p) :=
    fun x => (even_two_mul p).pow_abs _
  simp_rw [he]
  exact (le_abs_self _).trans hh

end Asakura.Chapter12
