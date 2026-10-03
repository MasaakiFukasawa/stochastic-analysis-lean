import Chapter8NewtonCoordinates

open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 1200000

/-- Both norm-comparison constants depend only on the two scalar
parameters of the quadratic form, not on the dimension. -/
theorem newton_euclidean_norm_comparison {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (δ b : ℝ) (hp : 0<b+δ^2/4) :
    let c := Real.sqrt (b+δ^2/4)
    ∀ z : E × E,
      ‖newtonCoordinateEquiv δ b hp z‖≤(c+1+|δ/2|)*‖WithLp.toLp 2 z‖ ∧
      ‖WithLp.toLp 2 z‖≤(1+(1+|δ/2|)*c⁻¹)*‖newtonCoordinateEquiv δ b hp z‖ := by
  dsimp only
  let c := Real.sqrt (b+δ^2/4)
  have hc : 0<c := Real.sqrt_pos.mpr hp
  have hsum (q v : E) : ‖WithLp.toLp 2 (q,v)‖≤‖q‖+‖v‖ := by
    have he := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (q,v))
    change ‖WithLp.toLp 2 (q,v)‖^2=‖q‖^2+‖v‖^2 at he
    nlinarith [norm_nonneg (WithLp.toLp 2 (q,v)),norm_nonneg q,norm_nonneg v]
  intro z
  let N := ‖newtonCoordinateEquiv δ b hp z‖
  let R := ‖WithLp.toLp 2 z‖
  have hq : ‖z.1‖≤R := WithLp.norm_fst_le E (WithLp.toLp 2 z)
  have hv : ‖z.2‖≤R := WithLp.norm_snd_le E (WithLp.toLp 2 z)
  have hnq : c*‖z.1‖≤N := by
    have hh := WithLp.norm_fst_le E (newtonCoordinateEquiv δ b hp z)
    change ‖c • z.1‖≤N at hh
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hc] using hh
  have hnv : ‖z.2+(δ/2) • z.1‖≤N := WithLp.norm_snd_le E (newtonCoordinateEquiv δ b hp z)
  have hnq' : ‖z.1‖≤c⁻¹*N := by
    have hh := mul_le_mul_of_nonneg_left hnq (inv_nonneg.mpr hc.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] using hh
  have hnv' : ‖z.2‖≤N+|δ/2| *‖z.1‖ := by
    have hh := norm_sub_le (z.2+(δ/2) • z.1) ((δ/2) • z.1)
    simp only [add_sub_cancel_right,norm_smul,Real.norm_eq_abs] at hh
    linarith
  constructor
  · have hh := hsum (c • z.1) (z.2+(δ/2) • z.1)
    have ha := norm_add_le z.2 ((δ/2) • z.1)
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hc] at hh ha
    change N≤_ at hh
    change N≤(c+1+|δ/2|)*R
    nlinarith [mul_le_mul_of_nonneg_left hq hc.le,
      mul_le_mul_of_nonneg_left hq (abs_nonneg (δ/2))]
  · have hh := hsum z.1 z.2
    change R≤_ at hh
    change R≤(1+(1+|δ/2|)*c⁻¹)*N
    nlinarith [mul_le_mul_of_nonneg_left hnq' (abs_nonneg (δ/2))]

end Asakura.Chapter8
