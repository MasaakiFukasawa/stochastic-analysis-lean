import Chapter12FiniteDivergence

namespace Asakura.Chapter12
open Asakura.FullAudit
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable def gaussianDivergence {n : ℕ}
    (u : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (du : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (z : Fin (n+1) → ℝ) : ℝ :=
  ∑ j : Fin (n+1), (z j*u j z-du j j z)

/-- Differentiate the displayed finite divergence. All coordinate derivatives
are actual HasDerivAt statements; the correction u_i comes from differentiating
z_j, and equality of mixed second derivatives is explicit. -/
theorem finite_divergence_commutation {n : ℕ}
    (u : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (du : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (ddu : Fin (n+1) → Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hu : ∀ i j z y, HasDerivAt (fun x => u j (i.insertNth (α := fun _ => ℝ) x z))
      (du i j (i.insertNth (α := fun _ => ℝ) y z)) y)
    (hdu : ∀ i j k z y, HasDerivAt (fun x => du j k (i.insertNth (α := fun _ => ℝ) x z))
      (ddu i j k (i.insertNth (α := fun _ => ℝ) y z)) y)
    (hsym : ∀ i j k z, ddu i j k z = ddu j i k z)
    (i : Fin (n+1)) (z : Fin n → ℝ) (y : ℝ) :
    HasDerivAt (fun x => gaussianDivergence u du (i.insertNth (α := fun _ => ℝ) x z))
      (u i (i.insertNth (α := fun _ => ℝ) y z) +
        ∑ j : Fin (n+1), ((i.insertNth (α := fun _ => ℝ) y z) j*du i j (i.insertNth (α := fun _ => ℝ) y z) -
          ddu j i j (i.insertNth (α := fun _ => ℝ) y z))) y := by
  classical
  have hj j := ((hasDerivAt_pi.mp (insertion_line_derivative i z y) j).mul
    (hu i j z y)).sub (hdu i j j z y)
  have h := HasDerivAt.sum (u := Finset.univ) (fun j _ => hj j)
  convert h using 1
  · ext x
    simp only [gaussianDivergence,Finset.sum_apply,Pi.mul_apply,Pi.sub_apply]
  · simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Pi.single_apply]
    simp_rw [hsym i]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    ring

end Asakura.Chapter12
