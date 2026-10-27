module

public import Certificates.Kernel.SporSch.PairJ3.F2239Forms
public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
public import Certificates.Data.Kernel.SporSch.PairJ3Cert
public meta import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
public meta import Certificates.Kernel.SporSch.J4S.Gen
public meta import CFSG.Certificates.Kernel.Common.StrChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#str_chunks CertificateChecks.KernelSporSch.PJ3I CFSG.Sporadic.Schreier.j3InvHex 810 100000 64

namespace CertificateChecks.KernelSporSch.F2239

open CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.Schreier.PairJ3 CFSG.Sporadic.SmallF2.Native in
meta def siN : Array Nat := invRowsF2 80 (spinVecs 80 TRows sepVec sepTree)

end CertificateChecks.KernelSporSch.F2239

#kss_rows CertificateChecks.KernelSporSch.F2239.RB CFSG.Sporadic.Schreier.PairJ3.BInv
#kss_rows CertificateChecks.KernelSporSch.F2239.SI CertificateChecks.KernelSporSch.F2239.siN

namespace CertificateChecks.KernelSporSch.F2239

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS CFSG.KS.SporSch CFSG.KS.SporSch.J3F
open CFSG.KD.J3F CFSG.Sporadic.Schreier.PairJ3 CertificateChecks.KernelSporSch

@[expose] noncomputable def INVW : Nat := hexLK PJ3I.c0

theorem invC : bAnd(le70K PJ3I.c0, wordsK (fun _ => INVW) 1 0 PJ3I.c0) = true := by quickRfl

theorem invLt : Nat.blt INVW (Nat.shiftLeft 1 3240) = true := by quickRfl

theorem pull1 : Nat.beq (imgK c rm t0 t1 t2 t3 t4 t5 t6 usK dgK A1 A1T INVW) INVW = true := by
  quickRfl

theorem pull2 : Nat.beq (imgK c rm t0 t1 t2 t3 t4 t5 t6 usK dgK A2 A2T INVW) INVW = true := by
  quickRfl

theorem prow : rows80K sepP.toList = true := by quickRfl

theorem binv : Nat.beq (mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 INVW)) dgK = true := by quickRfl

theorem sep : sepK c rm t0 t1 t2 t3 t4 t5 t6 dgK INVW RB [FW 0, FW 1, FW 2, FW 3] sepTerms sepVec
    sepIdx (packRowsK sepP.toList) sepTree SI = true := by quickRfl

end CertificateChecks.KernelSporSch.F2239

end
