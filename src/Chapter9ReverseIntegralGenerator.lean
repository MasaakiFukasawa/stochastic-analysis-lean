import Chapter9AdjointProduct

open MeasureTheory Finset
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

noncomputable def ouAdjoint {d : ℕ} (p : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin d => directional (directional p (Pi.single i 1)) (Pi.single i 1) x +
    directional (fun y : Fin d → ℝ => y i*p y) (Pi.single i 1) x)

noncomputable def ouBackward {d : ℕ} (k : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin d => directional (directional k (Pi.single i 1)) (Pi.single i 1) x -
    x i*directional k (Pi.single i 1) x)

noncomputable def reverseTest {d : ℕ} (p f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin d => directional (directional f (Pi.single i 1)) (Pi.single i 1) x +
    (x i+2*(directional p (Pi.single i 1) x/p x))*directional f (Pi.single i 1) x)

theorem ouAdjoint_smooth {d : ℕ} (p : (Fin d → ℝ) → ℝ) (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (ouAdjoint p) := by
  unfold ouAdjoint
  apply ContDiff.sum
  intro i _
  exact (directional_smooth _ (directional_smooth p hp _) _).add
    (directional_smooth _ (by fun_prop) _)

theorem ouBackward_smooth {d : ℕ} (k : (Fin d → ℝ) → ℝ) (hk : ContDiff ℝ ∞ k) :
    ContDiff ℝ ∞ (ouBackward k) := by
  unfold ouBackward
  apply ContDiff.sum
  intro i _
  exact (directional_smooth _ (directional_smooth k hk _) _).sub
    ((by fun_prop : ContDiff ℝ ∞ (fun x : Fin d → ℝ => x i)).mul
      (directional_smooth k hk _))

theorem ouAdjoint_compact_support {d : ℕ} (p : (Fin d → ℝ) → ℝ)
    (hp : HasCompactSupport p) : HasCompactSupport (ouAdjoint p) := by
  unfold ouAdjoint
  convert HasCompactSupport.finset_sum (s := Finset.univ)
    (fun i _ => ((hp.fderiv_apply ℝ (Pi.single i 1)).fderiv_apply ℝ (Pi.single i 1)).add
      ((hp.mul_left (f := fun y : Fin d → ℝ => y i)).fderiv_apply ℝ (Pi.single i 1))) using 1
  ext x
  simp only [Finset.sum_apply,Pi.add_apply,directional]
  rfl

/-- The actual integral identity in the reverse-generator proof: both
integrations by parts and all product derivatives have been discharged. -/
theorem reverse_integral_generator {d : ℕ} (f p k : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : ContDiff ℝ ∞ p) (hk : ContDiff ℝ ∞ k)
    (hfc : HasCompactSupport f) (hp0 : ∀ x,p x≠0) :
    (∫ x, -f x*ouAdjoint p x*k x + f x*p x*ouBackward k x)=
      ∫ x,p x*reverseTest p f x*k x := by
  have hi : Integrable (fun x => f x*ouAdjoint p x*k x) :=
    ((hf.continuous.mul (ouAdjoint_smooth p hp).continuous).mul hk.continuous).integrable_of_hasCompactSupport
      (hfc.mul_right.mul_right)
  have hj : Integrable (fun x => f x*p x*ouBackward k x) :=
    ((hf.continuous.mul hp.continuous).mul (ouBackward_smooth k hk).continuous).integrable_of_hasCompactSupport
      (hfc.mul_right.mul_right)
  have hl : Integrable (fun x => ouAdjoint (fun y => f y*p y) x*k x) :=
    ((ouAdjoint_smooth _ (hf.mul hp)).continuous.mul hk.continuous).integrable_of_hasCompactSupport
      (ouAdjoint_compact_support _ hfc.mul_right).mul_right
  have he := ou_adjoint_compact (fun y => f y*p y) k (hf.mul hp) hk hfc.mul_right
  change (∫ x,f x*p x*ouBackward k x)=(∫ x,ouAdjoint (fun y => f y*p y) x*k x) at he
  calc
    _ = -(∫ x,f x*ouAdjoint p x*k x)+(∫ x,f x*p x*ouBackward k x) := by
      simp_rw [neg_mul]
      have hadd := integral_add hi.neg hj
      simpa only [Pi.neg_apply,integral_neg] using hadd
    _ = (∫ x,ouAdjoint (fun y => f y*p y) x*k x)-(∫ x,f x*ouAdjoint p x*k x) := by rw [he]; ring
    _ = ∫ x,(ouAdjoint (fun y => f y*p y) x-f x*ouAdjoint p x)*k x := by
      rw [←integral_sub hl hi]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      dsimp only
      rw [show ouAdjoint (fun y => f y*p y) x-f x*ouAdjoint p x=p x*reverseTest p f x from
        actual_reverse_adjoint_product f p hf hp x (hp0 x)]
end Asakura.Chapter9
