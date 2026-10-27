module

public import Certificates.Data.Kernel.ThCent.Pin
public import Certificates.Kernel.ThCent.Data
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs

public section

namespace CFSG.KD.ThCent.Pin

open CFSG.KC.Th CFSG.KC.ThCent CFSG.SectionRank.Native CFSG.Sporadic.Th.Native

theorem a2 : Nat.beq (mulB ThS.c ThS.rm (ThS.RBf 1) (ThS.RBf 1)) ThS.ONE = true := by
  decide +kernel

theorem z3B : strictF (mulB ThS.c ThS.rm
    (wordZ ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x1Str))
    (wordZ ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x2Str)))
      (fun M => Nat.beq (BigS.powB ThS.c ThS.rm ThS.ONE M 9 4) W.Z3B) = true := by
  decide +kernel

theorem s3A : Nat.beq (runPk ThS.c ThS.rm ThS.ONE
    CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) 11) W.Z3A = true := by
  decide +kernel

theorem z7 : Nat.beq (runPk ThS.c ThS.rm ThS.ONE
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative.prog7 ++
      [.pow 6 25 43, .mul 24 43 44])
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) 44) W.Z7 = true := by
  decide +kernel

theorem neg_s3A : BigS.notB (Nat.beq (runPk ThS.c ThS.rm ThS.ONE
    CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) 12) W.Z3A) = true := by
  decide +kernel

theorem neg_z3B : BigS.notB (strictF (mulB ThS.c ThS.rm
    (wordZ ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x2Str))
    (wordZ ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) ThS.Bi (abWord x1Str)))
      (fun M => Nat.beq (BigS.powB ThS.c ThS.rm ThS.ONE M 3 4) W.Z3B)) = true := by
  decide +kernel

end CFSG.KD.ThCent.Pin

end
