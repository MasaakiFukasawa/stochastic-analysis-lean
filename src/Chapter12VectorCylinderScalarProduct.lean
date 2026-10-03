import Chapter12ScalarFromVectorFrame
import Chapter12CylinderProduct

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def VectorCylinderExpr.scalarProduct {H E:Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f:SmoothCylinder H) : VectorCylinderExpr H E → VectorCylinderExpr H E
  | .term c v => .term (mulSmoothCylinder f c) v
  | .sum n c => .sum n (fun i => (c i).scalarProduct f)
  | .smul a c => .smul a (c.scalarProduct f)

theorem VectorCylinderExpr.scalarProduct_rawValue {Ω H E:Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P:Measure Ω) (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (f:SmoothCylinder H) (c:VectorCylinderExpr H E) (w:Ω) :
    (c.scalarProduct f).rawValue P W w=f.value P W w • c.rawValue P W w := by
  induction c with
  | term c v => simp only [scalarProduct,rawValue,mulSmoothCylinder_value,mul_smul]
  | sum n c ih => simp only [scalarProduct,rawValue,ih,Finset.smul_sum]
  | smul a c ih =>
    change a • (c.scalarProduct f).rawValue P W w=f.value P W w • (a • c.rawValue P W w)
    rw [ih]
    exact smul_comm a (f.value P W w) (c.rawValue P W w)

theorem gaussian_vector_scalar_product_function {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N:ℕ} (f:GaussianJet N) (u:Fin N → GaussianJet N) (e:Fin N → H) :
    gaussianVectorFunction (fun i => f.mul (u i)) e=
      (fun z => f.f z • gaussianVectorFunction u e z) := by
  funext z
  simp only [gaussianVectorFunction,GaussianJet.mul,Finset.smul_sum,mul_smul]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.VectorCylinderExpr.scalarProduct_rawValue
