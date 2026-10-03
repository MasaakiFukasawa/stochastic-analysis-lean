import Chapter8SDEGeneratorInterface

open MeasureTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem bounded_derivative_coordinates {d : ℕ}
    (f : (Fin d → ℝ) → ℝ) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (ha : ∀ x,‖fderiv ℝ f x‖≤A) (hb : ∀ x,‖fderiv ℝ (fderiv ℝ f) x‖≤B) :
    (∀ x i,|fderiv ℝ f x (Pi.single i 1)|≤A) ∧
    (∀ x i j,|fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)|≤B) := by
  have he (i : Fin d) : ‖(Pi.single i 1 : Fin d → ℝ)‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro j
    by_cases h : j=i <;> simp [Pi.single_apply,h,eq_comm]
  constructor
  · intro x i
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ f x).le_opNorm _).trans
      ((mul_le_mul (ha x) (he i) (norm_nonneg _) hA).trans_eq (mul_one A))
  · intro x i j
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) x (Pi.single i 1)‖ * ‖(Pi.single j 1 : Fin d → ℝ)‖ :=
        (fderiv ℝ (fderiv ℝ f) x (Pi.single i 1)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) x‖ * ‖(Pi.single i 1 : Fin d → ℝ)‖) * ‖(Pi.single j 1 : Fin d → ℝ)‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ f) x).le_opNorm _) (norm_nonneg _)
      _ ≤ (B*1)*1 := mul_le_mul (mul_le_mul (hb x) (he i) (norm_nonneg _) hB)
        (he j) (norm_nonneg _) (by positivity)
      _ = B := by ring

/-- Bounded spatial derivatives and constant diffusion give the exact
linear growth needed to differentiate the Gibbs integral. -/
theorem generator_linear_growth {d n : ℕ}
    (b : (Fin d → ℝ) → (Fin d → ℝ)) (σ : Fin d → Fin n → ℝ)
    (Cb : ℝ) (hCb : 0≤Cb) (hbg : ∀ x,‖b x‖≤Cb*(1+‖x‖))
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃ C : ℝ,0≤C ∧ ∀ f : (Fin d → ℝ) → ℝ,
      (∀ x,‖fderiv ℝ f x‖≤A) → (∀ x,‖fderiv ℝ (fderiv ℝ f) x‖≤B) →
      ∀ x, |coordinateGenerator (fun i y => b y i) (fun i j _ => σ i j) f x|≤C*(1+‖x‖) := by
  let S := ∑ i : Fin d, ∑ j : Fin d, |∑ k : Fin n,σ i k*σ j k|
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  refine ⟨(d:ℝ)*A*Cb+B*S/2,by positivity,?_⟩
  intro f ha hb x
  obtain ⟨h1,h2⟩ := bounded_derivative_coordinates f A B hA hB ha hb
  have hd : |∑ i,fderiv ℝ f x (Pi.single i 1)*b x i|≤(d:ℝ)*A*Cb*(1+‖x‖) := by
    calc
      _ ≤ ∑ i,|fderiv ℝ f x (Pi.single i 1)*b x i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d,A*(Cb*(1+‖x‖)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        have hbi0 : |b x i|≤‖b x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (b x) i
        have hbi := hbi0.trans (hbg x)
        exact mul_le_mul (h1 x i) hbi (abs_nonneg _) hA
      _ = _ := by simp; ring
  have hs : |∑ i,∑ j,fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)*(∑ k,σ i k*σ j k)|≤B*S := by
    calc
      _ ≤ ∑ i,|∑ j,fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)*(∑ k,σ i k*σ j k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i,∑ j,B*|∑ k,σ i k*σ j k| := by
        apply Finset.sum_le_sum
        intro i _
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (h2 x i j) (abs_nonneg _)))
      _ = B*S := by simp only [S,Finset.mul_sum]
  unfold coordinateGenerator
  have ha' := abs_add_le (∑ i,fderiv ℝ f x (Pi.single i 1)*b x i)
    ((∑ i,∑ j,fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)*(∑ k,σ i k*σ j k))/2)
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at ha'
  have hn : 0≤B*S*‖x‖ := by positivity
  nlinarith

end Asakura.Chapter8
