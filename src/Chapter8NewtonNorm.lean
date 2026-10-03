import Chapter8NewtonIntegralPaths
import Mathlib.Analysis.InnerProductSpace.ProdL2

open scoped RealInnerProductSpace
namespace Asakura.Chapter8
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def newtonCoordinates (δ b : ℝ) (z : E × E) : WithLp 2 (E × E) :=
  WithLp.toLp 2 (Real.sqrt (b+δ^2/4) • z.1, z.2+(δ/2) • z.1)

def newtonNorm (δ b : ℝ) (z : E × E) : ℝ := ‖newtonCoordinates δ b z‖

theorem newton_norm_square (δ b : ℝ) (hp : 0 ≤ b+δ^2/4) (z : E × E) :
    (newtonNorm δ b z)^2 = newtonVectorEnergy δ b z.1 z.2 := by
  rw [newtonNorm,WithLp.prod_norm_sq_eq_of_L2]
  change ‖Real.sqrt (b+δ^2/4) • z.1‖^2 + ‖z.2+(δ/2) • z.1‖^2 = _
  rw [norm_smul,norm_add_sq_real,real_inner_smul_right,norm_smul]
  simp only [Real.norm_eq_abs,mul_pow,sq_abs,Real.sq_sqrt hp,newtonVectorEnergy]
  rw [real_inner_comm z.1 z.2]
  ring

theorem newton_coordinates_add (δ b : ℝ) (x y : E × E) :
    newtonCoordinates δ b (x+y) = newtonCoordinates δ b x+newtonCoordinates δ b y := by
  apply WithLp.ofLp_injective
  simp [newtonCoordinates,smul_add,add_assoc,add_left_comm,add_comm]

theorem newton_coordinates_smul (δ b a : ℝ) (x : E × E) :
    newtonCoordinates δ b (a • x) = a • newtonCoordinates δ b x := by
  apply WithLp.ofLp_injective
  change (Real.sqrt (b+δ^2/4) • (a • x.1),a • x.2+(δ/2) • (a • x.1)) =
    (a • (Real.sqrt (b+δ^2/4) • x.1),a • (x.2+(δ/2) • x.1))
  ext <;> module

theorem newton_norm_triangle (δ b : ℝ) (x y : E × E) :
    newtonNorm δ b (x+y) ≤ newtonNorm δ b x+newtonNorm δ b y := by
  unfold newtonNorm
  rw [newton_coordinates_add]
  exact norm_add_le _ _

theorem newton_norm_smul (δ b a : ℝ) (x : E × E) :
    newtonNorm δ b (a • x) = |a| *newtonNorm δ b x := by
  unfold newtonNorm
  rw [newton_coordinates_smul,norm_smul,Real.norm_eq_abs]

theorem newton_norm_eq_zero_iff (δ b : ℝ) (hp : 0 < b+δ^2/4) (x : E × E) :
    newtonNorm δ b x = 0 ↔ x = 0 := by
  rw [newtonNorm,norm_eq_zero]
  constructor
  · intro hx
    have hh := congrArg WithLp.ofLp hx
    change (Real.sqrt (b+δ^2/4) • x.1,x.2+(δ/2) • x.1) = (0,0) at hh
    have hq : x.1 = 0 := (smul_eq_zero.mp (congrArg Prod.fst hh)).resolve_left
      (Real.sqrt_pos.mpr hp).ne'
    have hv : x.2 = 0 := by simpa [hq] using congrArg Prod.snd hh
    exact Prod.ext hq hv
  · rintro rfl
    simp [newtonCoordinates]

end
end Asakura.Chapter8
