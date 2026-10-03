import Chapter8AveragedHessian

open scoped BigOperators
namespace Asakura.Chapter8
noncomputable section

/-- The Gibbs density and its derivative are obtained by the chain rule. -/
def gibbsDensity {E : Type*} (U : E → ℝ) (β Z : ℝ) (x : E) : ℝ :=
  Z⁻¹ * Real.exp (-β*U x)

theorem gibbs_density_positive {E : Type*} (U : E → ℝ) (β Z : ℝ)
    (hZ : 0 < Z) (x : E) : 0 < gibbsDensity U β Z x :=
  mul_pos (inv_pos.mpr hZ) (Real.exp_pos _)

theorem gibbs_density_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → ℝ) (DU : E →L[ℝ] ℝ) (β Z : ℝ) (x : E)
    (hU : HasFDerivAt U DU x) :
    HasFDerivAt (gibbsDensity U β Z) ((-β*gibbsDensity U β Z x) • DU) x := by
  have hh := ((hU.const_mul (-β)).exp).const_mul Z⁻¹
  convert hh using 1
  · rfl
  · ext v
    simp [gibbsDensity,ContinuousLinearMap.smul_apply]
    ring

/-- The Hamiltonian part cancels against the derivatives of the
Gibbs-Maxwell density, in every dimension. -/
theorem newton_hamiltonian_density_cancellation {ι : Type*} [Fintype ι]
    (β m ρ : ℝ) (hm : m ≠ 0) (v gradU : ι → ℝ) :
    (∑ i : ι, (v i * (-β*ρ*gradU i) - (gradU i/m)*(-β*m*ρ*v i))) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  field_simp
  <;> ring

/-- The velocity Einstein relation is exactly the divergence form of the
Ornstein-Uhlenbeck part of the Newton generator. -/
theorem newton_velocity_density_balance (β m γ ρ v : ℝ) (hβ : β ≠ 0) (hm : m ≠ 0) :
    -(γ/m)*v*ρ = γ/(β*m^2)*(-β*m*v*ρ) := by
  field_simp
  <;> ring

end
end Asakura.Chapter8
