import Chapter5PerturbationParameters

namespace Asakura.Chapter5
set_option maxHeartbeats 1800000

/-- Take square roots of the three actual a-priori energy bounds. The
printed coefficient involving lambda requires choosing lambda positive. -/
theorem perturbation_norm_coefficients
    (T C ell mu e d y z u : ℝ)
    (hT : 0 ≤ T) (hell : 0 < ell) (hgap : C < ell^2) (hmu : 0 < mu)
    (hd : 0 ≤ d) (hy : 0 ≤ y) (hz : 0 ≤ z) (hu : 0 ≤ u)
    (hY : y^2 ≤ T*(e^2*d^2/mu^2))
    (hZ : z^2 ≤ ell^2/(ell^2-C)*(e^2*d^2/mu^2))
    (hU : u^2 ≤ e^2*d^2/mu^2) :
    y ≤ |e| *(Real.sqrt T/mu)*d ∧
    z ≤ |e| *(ell/(mu*Real.sqrt (ell^2-C)))*d ∧
    u ≤ |e|/mu*d := by
  have hgap0 : 0 < ell^2-C := sub_pos.mpr hgap
  have hy0 : 0 ≤ |e| *(Real.sqrt T/mu)*d := by positivity
  have hz0 : 0 ≤ |e| *(ell/(mu*Real.sqrt (ell^2-C)))*d := by positivity
  have hu0 : 0 ≤ |e|/mu*d := by positivity
  have hysq : (|e| *(Real.sqrt T/mu)*d)^2 = T*(e^2*d^2/mu^2) := by
    rw [mul_pow,mul_pow,div_pow,sq_abs,Real.sq_sqrt hT]
    ring
  have hzsq : (|e| *(ell/(mu*Real.sqrt (ell^2-C)))*d)^2 = ell^2/(ell^2-C)*(e^2*d^2/mu^2) := by
    rw [mul_pow,mul_pow,div_pow,mul_pow,sq_abs,Real.sq_sqrt hgap0.le]
    field_simp
    <;> ring
  have husq : (|e|/mu*d)^2 = e^2*d^2/mu^2 := by
    rw [mul_pow,div_pow,sq_abs]
    ring
  exact ⟨(sq_le_sq₀ hy hy0).mp (hY.trans_eq hysq.symm),
    (sq_le_sq₀ hz hz0).mp (hZ.trans_eq hzsq.symm),(sq_le_sq₀ hu hu0).mp (hU.trans_eq husq.symm)⟩

end Asakura.Chapter5
