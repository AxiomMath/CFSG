module

public import Certificates.Data.Kernel.E6TT.EnumSplit
public import Certificates.Data.Kernel.E6TT.Row
public import Certificates.Kernel.E6TT.Data
public import Certificates.Kernel.E6TT.WeylData
public import Certificates.Kernel.E6TT.RowData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE6TT

open CFSG.KC.E6TT Certificates.Data.E6TableT

theorem rootsV : (vecs RV.V 72 == roots ()) = true := by quickRfl

theorem hsA2 : hsK W.H0 = true := by quickRfl

theorem hsA4A1 : hsK W.H1 = true := by quickRfl

theorem hsD4 : hsK W.H2 = true := by quickRfl

theorem hsA5 : hsK W.H3 = true := by quickRfl

theorem hsD5 : hsK W.H4 = true := by quickRfl

theorem mapsA4A1 :
    Nat.beq (enumK D.GR D.L1 D.N11 D.N12 D.N13 D.N14 D.N15 (leafK 1 W.H1 W.O1 RV.V)) 0 = true := by
  quickRfl

theorem mapsD4_e0 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      D.L2) 0 = true := by
  quickRfl

theorem mapsD4_e1 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight D.L2 (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e2 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e3 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e4 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e5 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e6 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e7 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e8 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e9 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e10 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e11 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e12 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e13 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e14 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e15 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e16 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_e17 :
    Nat.beq (sumP 1 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_q1 :
    Nat.beq (sumP 18 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1))) 0 = true := by
  quickRfl

theorem mapsD4_q2 :
    Nat.beq (sumP 18 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 18))) 0 = true := by
  quickRfl

theorem mapsD4_q3 :
    Nat.beq (sumP 18 (enumBody D.GR D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L2 (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 1)) (7 * 18)) (7 * 18))) 0 = true := by
  quickRfl

theorem mapsD4 :
    Nat.beq (enumK D.GR D.L2 D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V)) 0 = true := by
  rw [enumK_eq]
  refine sumP_zero_of_parts 1 71 72 rfl mapsD4_e0 ?_
  refine sumP_zero_of_parts 1 70 71 rfl mapsD4_e1 ?_
  refine sumP_zero_of_parts 1 69 70 rfl mapsD4_e2 ?_
  refine sumP_zero_of_parts 1 68 69 rfl mapsD4_e3 ?_
  refine sumP_zero_of_parts 1 67 68 rfl mapsD4_e4 ?_
  refine sumP_zero_of_parts 1 66 67 rfl mapsD4_e5 ?_
  refine sumP_zero_of_parts 1 65 66 rfl mapsD4_e6 ?_
  refine sumP_zero_of_parts 1 64 65 rfl mapsD4_e7 ?_
  refine sumP_zero_of_parts 1 63 64 rfl mapsD4_e8 ?_
  refine sumP_zero_of_parts 1 62 63 rfl mapsD4_e9 ?_
  refine sumP_zero_of_parts 1 61 62 rfl mapsD4_e10 ?_
  refine sumP_zero_of_parts 1 60 61 rfl mapsD4_e11 ?_
  refine sumP_zero_of_parts 1 59 60 rfl mapsD4_e12 ?_
  refine sumP_zero_of_parts 1 58 59 rfl mapsD4_e13 ?_
  refine sumP_zero_of_parts 1 57 58 rfl mapsD4_e14 ?_
  refine sumP_zero_of_parts 1 56 57 rfl mapsD4_e15 ?_
  refine sumP_zero_of_parts 1 55 56 rfl mapsD4_e16 ?_
  refine sumP_zero_of_parts 1 54 55 rfl mapsD4_e17 ?_
  refine sumP_zero_of_parts 18 36 54 rfl mapsD4_q1 ?_
  refine sumP_zero_of_parts 18 18 36 rfl mapsD4_q2 ?_
  exact mapsD4_q3

theorem mapsA5_q0 :
    Nat.beq (sumP 18 (enumBody D.GR D.N31 D.N32 D.N33 D.N34 D.N35 (leafK 3 W.H3 W.O3 RV.V))
      D.L3) 0 = true := by
  quickRfl

theorem mapsA5_q1 :
    Nat.beq (sumP 18 (enumBody D.GR D.N31 D.N32 D.N33 D.N34 D.N35 (leafK 3 W.H3 W.O3 RV.V))
      (Nat.shiftRight D.L3 (7 * 18))) 0 = true := by
  quickRfl

theorem mapsA5_q2 :
    Nat.beq (sumP 18 (enumBody D.GR D.N31 D.N32 D.N33 D.N34 D.N35 (leafK 3 W.H3 W.O3 RV.V))
      (Nat.shiftRight (Nat.shiftRight D.L3 (7 * 18)) (7 * 18))) 0 = true := by
  quickRfl

theorem mapsA5_q3 :
    Nat.beq (sumP 18 (enumBody D.GR D.N31 D.N32 D.N33 D.N34 D.N35 (leafK 3 W.H3 W.O3 RV.V))
      (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight D.L3 (7 * 18)) (7 * 18)) (7 * 18))) 0 = true := by
  quickRfl

theorem mapsA5 :
    Nat.beq (enumK D.GR D.L3 D.N31 D.N32 D.N33 D.N34 D.N35 (leafK 3 W.H3 W.O3 RV.V)) 0 = true := by
  rw [enumK_eq]
  refine sumP_zero_of_parts 18 54 72 rfl mapsA5_q0 ?_
  refine sumP_zero_of_parts 18 36 54 rfl mapsA5_q1 ?_
  refine sumP_zero_of_parts 18 18 36 rfl mapsA5_q2 ?_
  exact mapsA5_q3

theorem mapsD5 :
    Nat.beq (enumK D.GR D.L4 D.N41 D.N42 D.N43 D.N44 D.N45 (leafK 4 W.H4 W.O4 RV.V)) 0 = true := by
  quickRfl

end CertificateChecks.KernelE6TT

end
