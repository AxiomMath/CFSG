module

public import Certificates.Kernel.HeLoc.FiveLDefs
public meta import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Five

open CFSG.Monster.B.Co2.Native

meta def qwM : List Nat :=
  let q0 := CFSG.RankThree.PartOne.heFiveQGens[0]!
  let q1 := CFSG.RankThree.PartOne.heFiveQGens[1]!
  CFSG.RankThree.PartOne.heFiveC0Cert.pts.toList.map fun p =>
    ((List.range 8330).find? fun x =>
      let px := p[x]!
      let a0 := q0[x]!
      let a1 := q1[x]!
      p[a0]! != q0[px]! || p[a1]! != q1[px]!).getD 8330

meta def negM : List Nat :=
  let C := CFSG.RankThree.PartOne.heFiveC0Cert.pts
  [((List.range C.size).find? fun i =>
    qwM.getD i 0 != 8330 && !eqA 8330 (CFSG.Monster.B.Mathieu.powArr 8330 C[i]! 5) (idA 8330)).getD 0]

end CertificateChecks.KernelHeLoc.Five

#knatlist CertificateChecks.KernelHeLoc.Five.QW CertificateChecks.KernelHeLoc.Five.qwM
#knatlist CertificateChecks.KernelHeLoc.Five.QN CertificateChecks.KernelHeLoc.Five.negM

namespace CertificateChecks.KernelHeLoc.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KC.HeLoc

@[expose] noncomputable def qcAtW (i w : Nat) : Bool :=
  bIf(Nat.beq w 8330,
    bAnd(Nat.beq (trQ q C0.P C0.L 600 i) 0, eqOnL bs (powF (tv i) 5) (fun x => x)),
    bAnd(Nat.blt w 8330,
      bIf(Nat.beq (tv i (FiveL.pa 0 w)) (FiveL.pa 0 (tv i w)),
        bIf(Nat.beq (tv i (FiveL.pa 1 w)) (FiveL.pa 1 (tv i w)), false, true), true)))

@[expose] noncomputable def qcAt (i : Nat) : Bool := strictB (QW.getD i 0) (qcAtW i)

theorem kQC : CFSG.KC.Enum.allN 600 qcAt = true := by quickRfl

theorem qcNeg0 : (!qcAtW 0 0) = true := by quickRfl

theorem qcNeg1 : (!qcAtW (QN.getD 0 0) 8330) = true := by quickRfl

end CertificateChecks.KernelHeLoc.Five

end
