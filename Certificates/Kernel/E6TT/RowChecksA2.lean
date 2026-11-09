module

public import Certificates.Data.Kernel.E6TT.EnumSplit
public import Certificates.Data.Kernel.E6TT.RowA2
public import Certificates.Kernel.E6TT.Data
public import Certificates.Kernel.E6TT.WeylData
public import Certificates.Kernel.E6TT.RowData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE6TT

open CFSG.KC.E6TT Certificates.Data.E6TableT

theorem mapsA2F_e0 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      D.L0) 0 = true := by
  quickRfl

theorem mapsA2F_e1 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight D.L0 (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e2 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e3 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e4 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e5 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e6 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e7 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e8 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e9 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e10 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e11 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e12 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e13 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e14 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e15 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e16 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_e17 :
    Nat.beq (sumP 1 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_q1 :
    Nat.beq (sumP 18 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsA2F_q2 :
    Nat.beq (sumP 18 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 18))) 0 = true := by
  quickRfl

theorem mapsA2F_q3 :
    Nat.beq (sumP 18 (enumBody D.GR D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L0 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 18)) (7 * 18))) 0 = true := by
  quickRfl

theorem mapsA2F :
    Nat.beq (enumK D.GR D.L0 D.N01 D.N02 D.N03 D.N04 D.N05 (leafKA2 W.H0 W.O0 RV.V)) 0 = true := by
  rw [enumK_eq]
  refine sumP_zero_of_parts 1 71 72 rfl mapsA2F_e0 ?_
  refine sumP_zero_of_parts 1 70 71 rfl mapsA2F_e1 ?_
  refine sumP_zero_of_parts 1 69 70 rfl mapsA2F_e2 ?_
  refine sumP_zero_of_parts 1 68 69 rfl mapsA2F_e3 ?_
  refine sumP_zero_of_parts 1 67 68 rfl mapsA2F_e4 ?_
  refine sumP_zero_of_parts 1 66 67 rfl mapsA2F_e5 ?_
  refine sumP_zero_of_parts 1 65 66 rfl mapsA2F_e6 ?_
  refine sumP_zero_of_parts 1 64 65 rfl mapsA2F_e7 ?_
  refine sumP_zero_of_parts 1 63 64 rfl mapsA2F_e8 ?_
  refine sumP_zero_of_parts 1 62 63 rfl mapsA2F_e9 ?_
  refine sumP_zero_of_parts 1 61 62 rfl mapsA2F_e10 ?_
  refine sumP_zero_of_parts 1 60 61 rfl mapsA2F_e11 ?_
  refine sumP_zero_of_parts 1 59 60 rfl mapsA2F_e12 ?_
  refine sumP_zero_of_parts 1 58 59 rfl mapsA2F_e13 ?_
  refine sumP_zero_of_parts 1 57 58 rfl mapsA2F_e14 ?_
  refine sumP_zero_of_parts 1 56 57 rfl mapsA2F_e15 ?_
  refine sumP_zero_of_parts 1 55 56 rfl mapsA2F_e16 ?_
  refine sumP_zero_of_parts 1 54 55 rfl mapsA2F_e17 ?_
  refine sumP_zero_of_parts 18 36 54 rfl mapsA2F_q1 ?_
  refine sumP_zero_of_parts 18 18 36 rfl mapsA2F_q2 ?_
  exact mapsA2F_q3

end CertificateChecks.KernelE6TT

end
