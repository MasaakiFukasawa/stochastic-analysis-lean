import Chapter12CylinderFromSmooth
import Mathlib.Data.Fin.Tuple.Basic

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

noncomputable def cylinderLeftBlock (m n : ℕ) : (Fin (m+n) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Fin.castAdd n i))
noncomputable def cylinderRightBlock (m n : ℕ) : (Fin (m+n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Fin.natAdd m i))

@[simp] theorem cylinderLeftBlock_left (m n : ℕ) (i : Fin m) :
    cylinderLeftBlock m n (Pi.single (Fin.castAdd n i) 1) = Pi.single i 1 := by
  ext j
  simp [cylinderLeftBlock,Pi.single_apply,Fin.castAdd_inj]

@[simp] theorem cylinderLeftBlock_right (m n : ℕ) (i : Fin n) :
    cylinderLeftBlock m n (Pi.single (Fin.natAdd m i) 1) = 0 := by
  ext j
  have hne : Fin.castAdd n j ≠ Fin.natAdd m i := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  simp [cylinderLeftBlock,Pi.single_apply,hne]

@[simp] theorem cylinderRightBlock_left (m n : ℕ) (i : Fin m) :
    cylinderRightBlock m n (Pi.single (Fin.castAdd n i) 1) = 0 := by
  ext j
  have hne : Fin.natAdd m j ≠ Fin.castAdd n i := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  simp [cylinderRightBlock,Pi.single_apply,hne]

@[simp] theorem cylinderRightBlock_right (m n : ℕ) (i : Fin n) :
    cylinderRightBlock m n (Pi.single (Fin.natAdd m i) 1) = Pi.single i 1 := by
  ext j
  simp [cylinderRightBlock,Pi.single_apply,Fin.natAdd_inj]

end Asakura.Chapter12
