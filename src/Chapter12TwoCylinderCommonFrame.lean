import Chapter12ScalarCylinderCommonFrame

open MeasureTheory
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem two_cylinder_common_frame {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (c d : SmoothCylinder H) :
    ∃n:ℕ,∃e:Fin (n+1) → H,∃f g : GaussianJet (n+1),Orthonormal ℝ e ∧
      c.value P W=ᵐ[P] (f.toCylinder e).value P W ∧
      d.value P W=ᵐ[P] (g.toCylinder e).value P W := by
  obtain ⟨n,e,f,he,hf⟩ := scalar_cylinders_common_frame P W (fun i : Fin 2 => if i=0 then c else d)
  exact ⟨n,e,f 0,f 1,he,by simpa using hf 0,by simpa using hf 1⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.two_cylinder_common_frame
