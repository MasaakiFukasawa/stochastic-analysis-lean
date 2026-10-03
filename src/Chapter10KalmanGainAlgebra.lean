import Chapter10ErrorNoiseGram

open Matrix
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- The gain identity follows from the two inverse identities for D. -/
theorem kalman_gain_times_noise_covariance {d r : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (C : Matrix (Fin r) (Fin d) ℝ)
    (D J : Matrix (Fin r) (Fin r) ℝ) (hJD : J*D=1) (hDJ : D*J=1) :
    (S*C.transpose*(J.transpose*J))*(D*D.transpose)=S*C.transpose := by
  have hjt : J.transpose*D.transpose=1 := by
    simpa only [transpose_mul,transpose_one] using congrArg Matrix.transpose hDJ
  calc
    _ = S*C.transpose*J.transpose*(J*D)*D.transpose := by simp only [Matrix.mul_assoc]
    _ = S*C.transpose*(J.transpose*D.transpose) := by rw [hJD]; simp only [Matrix.mul_one,Matrix.mul_assoc]
    _ = _ := by rw [hjt,Matrix.mul_one]

theorem kalman_gain_riccati_term {d r : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (C : Matrix (Fin r) (Fin d) ℝ)
    (J : Matrix (Fin r) (Fin r) ℝ) :
    (S*C.transpose*(J.transpose*J))*C*S=S*(C.transpose*(J.transpose*J)*C)*S := by
  simp only [Matrix.mul_assoc]

theorem kalman_information_symmetric {d r : ℕ}
    (C : Matrix (Fin r) (Fin d) ℝ) (J : Matrix (Fin r) (Fin r) ℝ) :
    (C.transpose*(J.transpose*J)*C).transpose=C.transpose*(J.transpose*J)*C := by
  simp only [transpose_mul,transpose_transpose,Matrix.mul_assoc]

end Asakura.Chapter10
