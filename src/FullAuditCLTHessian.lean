import FullAuditCLTTaylor

open MeasureTheory Set
namespace Asakura.FullAudit

noncomputable def cltHessianRemainder (Fxx Fxt Ftt : ℝ → ℝ) (x v : ℝ) : ℝ :=
  x^2*(∫ s in (0:ℝ)..1, (Fxx s-Fxx 0)*(1-s)) -
    2*x*v*(∫ s in (0:ℝ)..1, Fxt s*(1-s)) +
    v^2*(∫ s in (0:ℝ)..1, Ftt s*(1-s))

/-- The complete A+B+D estimate in the displayed Hessian remainder, including
both small and large space-time increments. -/
theorem clt_hessian_remainder_bound (Fxx Fxt Ftt : ℝ → ℝ)
    (hxx : ContinuousOn Fxx (Icc 0 1)) (hxt : ContinuousOn Fxt (Icc 0 1))
    (htt : ContinuousOn Ftt (Icc 0 1)) (C₂ C₃ x v ε : ℝ)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hv : 0 ≤ v) (hε : 0 < ε)
    (hbxx : ∀ s ∈ Icc (0:ℝ) 1, |Fxx s| ≤ C₂)
    (hbxt : ∀ s ∈ Icc (0:ℝ) 1, |Fxt s| ≤ C₂)
    (hbtt : ∀ s ∈ Icc (0:ℝ) 1, |Ftt s| ≤ C₂)
    (hthird : ∀ s ∈ Icc (0:ℝ) 1, |Fxx s-Fxx 0| ≤ C₃*(|x|+v)*s) :
    |cltHessianRemainder Fxx Fxt Ftt x v| ≤
      C₂*(v^2+v*|x|+x^2*(if (2*ε)^2 ≤ x^2+v^2 then 1 else 0))+ε*C₃*x^2 := by
  let I : ℝ := if (2*ε)^2 ≤ x^2+v^2 then 1 else 0
  let A := x^2*(∫ s in (0:ℝ)..1, (Fxx s-Fxx 0)*(1-s))
  let B := -2*x*v*(∫ s in (0:ℝ)..1, Fxt s*(1-s))
  let D := v^2*(∫ s in (0:ℝ)..1, Ftt s*(1-s))
  have hA : |A| ≤ C₂*x^2*I+ε*C₃*x^2 := by
    have hAc : ContinuousOn (fun s => Fxx s-Fxx 0) (Icc 0 1) := hxx.sub continuousOn_const
    by_cases hl : (2*ε)^2 ≤ x^2+v^2
    · have hbd := clt_weighted_bound (fun s => Fxx s-Fxx 0) hAc (2*C₂) (by positivity) (by
        intro s hs
        exact (abs_sub_le (Fxx s) 0 (Fxx 0)).trans (by simpa only [sub_zero,zero_sub,abs_neg,two_mul] using add_le_add (hbxx s hs) (hbxx 0 ⟨le_rfl,zero_le_one⟩)))
      dsimp [A,I]
      rw [if_pos hl,abs_mul,abs_of_nonneg (sq_nonneg x),mul_one]
      have hh := mul_le_mul_of_nonneg_left hbd (sq_nonneg x)
      nlinarith [mul_nonneg (mul_nonneg hε.le hC₃) (sq_nonneg x)]
    · have hx : |x| ≤ 2*ε := by
        have hh := lt_of_not_ge hl
        nlinarith [sq_abs x,sq_nonneg v,abs_nonneg x]
      have hvs : v ≤ 2*ε := by
        have hh := lt_of_not_ge hl
        nlinarith [sq_nonneg x]
      have hbd := clt_weighted_linear_bound (fun s => Fxx s-Fxx 0) hAc (C₃*(|x|+v))
        (mul_nonneg hC₃ (add_nonneg (abs_nonneg x) hv)) hthird
      have hs := Asakura.Chapter1Written.small_increment_constant x v ε C₃ hv hε.le hC₃ hx hvs
      dsimp [A,I]
      rw [if_neg hl,mul_zero,zero_add,abs_mul,abs_of_nonneg (sq_nonneg x)]
      exact (mul_le_mul_of_nonneg_left hbd (sq_nonneg x)).trans (by nlinarith)
  have hB : |B| ≤ C₂*v*|x| := by
    have hi := clt_weighted_bound Fxt hxt C₂ hC₂ hbxt
    have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * |x| * v by positivity)
    dsimp [B]
    simp only [abs_mul,abs_neg,abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num),abs_of_nonneg hv]
    nlinarith
  have hD : |D| ≤ C₂*v^2/2 := by
    have hi := clt_weighted_bound Ftt htt C₂ hC₂ hbtt
    dsimp [D]
    rw [abs_mul,abs_of_nonneg (sq_nonneg v)]
    have hh := mul_le_mul_of_nonneg_left hi (sq_nonneg v)
    nlinarith
  have h := Asakura.Chapter1Written.remainder_assembly x v ε C₂ C₃ A B D I hC₂ hv hA hB hD
  have he : A+B+D = cltHessianRemainder Fxx Fxt Ftt x v := by dsimp [A,B,D,cltHessianRemainder]; ring
  rwa [he] at h

/-- Once the variance is at most epsilon, the space-time tail is absorbed
by the ordinary Lindeberg tail in the manuscript. -/
theorem clt_hessian_lindeberg_bound (Fxx Fxt Ftt : ℝ → ℝ)
    (hxx : ContinuousOn Fxx (Icc 0 1)) (hxt : ContinuousOn Fxt (Icc 0 1))
    (htt : ContinuousOn Ftt (Icc 0 1)) (C₂ C₃ x v ε : ℝ)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hv : 0 ≤ v) (hε : 0 < ε) (hvε : v ≤ ε)
    (hbxx : ∀ s ∈ Icc (0:ℝ) 1, |Fxx s| ≤ C₂)
    (hbxt : ∀ s ∈ Icc (0:ℝ) 1, |Fxt s| ≤ C₂)
    (hbtt : ∀ s ∈ Icc (0:ℝ) 1, |Ftt s| ≤ C₂)
    (hthird : ∀ s ∈ Icc (0:ℝ) 1, |Fxx s-Fxx 0| ≤ C₃*(|x|+v)*s) :
    |cltHessianRemainder Fxx Fxt Ftt x v| ≤
      C₂*(v^2+v*|x|+(if ε ≤ |x| then x^2 else 0))+ε*C₃*x^2 := by
  have h := clt_hessian_remainder_bound Fxx Fxt Ftt hxx hxt htt C₂ C₃ x v ε hC₂ hC₃ hv hε hbxx hbxt hbtt hthird
  have ht : x^2*(if (2*ε)^2 ≤ x^2+v^2 then 1 else 0) ≤ (if ε ≤ |x| then x^2 else 0) := by
    by_cases hl : (2*ε)^2 ≤ x^2+v^2
    · have hx := Asakura.Chapter1Written.large_increment x v ε hv hε hvε hl
      simp [hl,hx]
    · by_cases hx : ε ≤ |x| <;> simp [hl,hx,sq_nonneg x]
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl ht) hC₂) le_rfl)

end Asakura.FullAudit
