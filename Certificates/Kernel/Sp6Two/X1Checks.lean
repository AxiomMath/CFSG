module

public import Certificates.Data.Kernel.Sp62X1
public import Certificates.Data.Kernel.Sp6TwoK
public import Certificates.Data.Kernel.Sp6TwoT
public import Certificates.Data.Sp62.Involutions
public import Certificates.Kernel.Sp6Two.Rec
public import Certificates.Kernel.Sp6Two.X1Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp62X1

open CFSG.KD.Sp62 CFSG.KD.Sp6Two CFSG.KC.Loop CFSG.Quasithin.H13.U3

@[expose] noncomputable def invL : List Nat :=
  ((List.range 512).map (recX REC 34728)).filter invN

@[expose] noncomputable def peelL : List Nat := sp62PeelSeq.map pk

theorem tabA_ok : (Nat.beq (recX XR 16 0) ONE &&
    tableKG XR (rmulSt (at2 XR 0)) 16 64 6 1 6 1) = true := by quickRfl

theorem abelA_ok : allBelow 64 1 (fun i => Nat.beq (MULF (recX XR 16 i) (recX XR 16 i)) ONE &&
    allBelow 64 1 (fun j => commN (recX XR 16 i) (recX XR 16 j))) = true := by quickRfl

theorem gensA_ok : allBelow 6 1 (fun s => inTab REC 34728 512 (at2 XR 6 s) (at2 XR 0 s)) = true := by
  quickRfl

theorem peelA_ok : peelN 62 invL peelL = true := by quickRfl

theorem y0A_ok : (inTab REC 29 63 (XR 12) (pk sp62Y0) &&
    allL (fun w => commN w (pk sp62Y0)) (resN invL peelL)) = true := by quickRfl

theorem y1A_ok : (inTab REC 93 315 (XR 13) (pk sp62Y1) &&
    allL (fun w => commN w (pk sp62Y1)) (resN invL peelL)) = true := by quickRfl

theorem y2A_ok : (inTab REC 409 945 (XR 14) (pk sp62Y2) &&
    allL (fun w => commN w (pk sp62Y2)) (resN invL peelL)) = true := by quickRfl

theorem y3A_ok : (inTab REC 1355 3780 (XR 15) (pk sp62Y3) &&
    allL (fun w => commN w (pk sp62Y3)) (resN invL peelL)) = true := by quickRfl

end CFSG.KD.Sp62X1

end
