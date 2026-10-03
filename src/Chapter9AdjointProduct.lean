import Chapter9CompactAdjoint

open Finset
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

 theorem directional_product {d : ℕ} (f g : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v x : Fin d → ℝ) :
    directional (fun y => f y*g y) v x=directional f v x*g x+f x*directional g v x := by
  have h := ((hf.differentiable (by simp) x).hasFDerivAt.mul
    (hg.differentiable (by simp) x).hasFDerivAt).fderiv
  dsimp [directional]
  change (fderiv ℝ (f * g) x) v = _
  rw [h]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

 theorem directional_sum {d : ℕ} (f g : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v x : Fin d → ℝ) :
    directional (fun y => f y+g y) v x=directional f v x+directional g v x := by
  have h := ((hf.differentiable (by simp) x).hasFDerivAt.add
    (hg.differentiable (by simp) x).hasFDerivAt).fderiv
  dsimp [directional]
  change (fderiv ℝ (f + g) x) v = _
  rw [h,add_apply]

 theorem directional_product_twice {d : ℕ} (f g : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v x : Fin d → ℝ) :
    directional (directional (fun y => f y*g y) v) v x=
      g x*directional (directional f v) v x+
      2*directional f v x*directional g v x+f x*directional (directional g v) v x := by
  have he : directional (fun y => f y*g y) v=
      (fun y => directional f v y*g y+f y*directional g v y) :=
    funext (fun y => directional_product f g hf hg v y)
  rw [he,directional_sum _ _ ((directional_smooth f hf v).mul hg)
    (hf.mul (directional_smooth g hg v)),
    directional_product _ _ (directional_smooth f hf v) hg,
    directional_product _ _ hf (directional_smooth g hg v)]
  ring

 theorem directional_coordinate_product {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (i : Fin d) (x : Fin d → ℝ) :
    directional (fun y : Fin d → ℝ => y i*f y) (Pi.single i 1) x=
      f x+x i*directional f (Pi.single i 1) x := by
  rw [directional_product _ _ (by fun_prop) hf]
  have he : directional (fun y : Fin d → ℝ => y i) (Pi.single i 1) x=1 := by
    dsimp [directional]
    change (fderiv ℝ (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) x) (Pi.single i 1)=1
    rw [ContinuousLinearMap.fderiv]
    simp
  rw [he,one_mul]

/-- The reverse generator's product identity uses actual first and second
spatial derivatives, not placeholders for formal coefficients. -/
theorem actual_reverse_adjoint_product {d : ℕ} (f p : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : ContDiff ℝ ∞ p) (x : Fin d → ℝ) (hpx : p x≠0) :
    (Finset.sum Finset.univ (fun i : Fin d =>directional (directional (fun y => f y*p y) (Pi.single i 1)) (Pi.single i 1) x+
      directional (fun y : Fin d → ℝ => y i*(f y*p y)) (Pi.single i 1) x))-
    f x*(Finset.sum Finset.univ (fun i : Fin d =>directional (directional p (Pi.single i 1)) (Pi.single i 1) x+
      directional (fun y : Fin d → ℝ => y i*p y) (Pi.single i 1) x))=
    p x*(Finset.sum Finset.univ (fun i : Fin d =>directional (directional f (Pi.single i 1)) (Pi.single i 1) x+
      (x i+2*(directional p (Pi.single i 1) x/p x))*directional f (Pi.single i 1) x)) := by
  simp_rw [directional_product_twice f p hf hp,
    directional_coordinate_product (fun y => f y*p y) (hf.mul hp),
    directional_coordinate_product p hp,directional_product f p hf hp]
  simpa only [mul_comm] using reverse_generator_product (p x) (f x) hpx x
    (fun i => directional p (Pi.single i 1) x) (fun i => directional f (Pi.single i 1) x)
    (fun i => directional (directional p (Pi.single i 1)) (Pi.single i 1) x)
    (fun i => directional (directional f (Pi.single i 1)) (Pi.single i 1) x)
end Asakura.Chapter9
