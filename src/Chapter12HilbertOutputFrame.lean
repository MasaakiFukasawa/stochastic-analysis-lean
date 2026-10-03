import Chapter12TensorCoordinateNorm

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

noncomputable def vectorMalliavinTensorPower (H K : RealHilbertSpaceData) : ℕ → RealHilbertSpaceData
  | 0 => hilbertTensorData H K
  | j+1 => hilbertTensorData H (vectorMalliavinTensorPower H K j)

noncomputable def vectorTensorFrame (H K : RealHilbertSpaceData) {N k : ℕ}
    (e : Fin N → H) (v : Fin k → K) :
    (j : ℕ) → (Fin k × (Fin (j+1) → Fin N)) → vectorMalliavinTensorPower H K j
  | 0,ab => hilbertPureTensor (e (ab.2 0)) (v ab.1)
  | j+1,ab => hilbertPureTensor (e (ab.2 0)) (vectorTensorFrame H K e v j (ab.1,Fin.tail ab.2))

theorem vectorTensorFrame_orthonormal (H K : RealHilbertSpaceData) {N k : ℕ}
    (e : Fin N → H) (v : Fin k → K) (he : Orthonormal ℝ e) (hv : Orthonormal ℝ v)
    (j : ℕ) : Orthonormal ℝ (vectorTensorFrame H K e v j) := by
  classical
  induction j with
  | zero =>
    apply (completed_tensor_orthonormal e v he hv).comp (fun ab : Fin k × (Fin 1 → Fin N) => (ab.2 0,ab.1))
    intro a b hab
    apply Prod.ext (congrArg Prod.snd hab)
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    simpa only [hi] using congrArg Prod.fst hab
  | succ j ih =>
    apply (completed_tensor_orthonormal e (vectorTensorFrame H K e v j) he ih).comp
      (fun ab : Fin k × (Fin (j+1+1) → Fin N) => (ab.2 0,(ab.1,Fin.tail ab.2)))
    intro a b hab
    have hfirst : a.1=b.1 := congrArg (fun x => x.2.1) hab
    refine Prod.ext hfirst ?_
    funext i
    refine Fin.cases ?_ (fun r => ?_) i
    · exact congrArg Prod.fst hab
    · exact congrFun (congrArg (fun x => x.2.2) hab) r

end Asakura.Chapter12
