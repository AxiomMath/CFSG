module

public import Certificates.Kernel.Sporadic.J3C.Data
public import Certificates.Kernel.SchreierFam.J3Cq
public import Certificates.Data.Kernel.Spor.CentReg
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelSpor.J3C

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.CentReg
  CFSG.ClassicalInvolution.J3Data CertificateChecks.KernelSpor.J3K
  CertificateChecks.KernelSchreierFam.J3Cq

@[expose] noncomputable def KLr (l x : Nat) : Nat := r32 KL (Nat.add (Nat.mul l (nat_lit 20520)) x)

@[expose] noncomputable def UL (i x : Nat) : Nat := wEval KLr (List.getD uWordsK i List.nil) x

@[expose] noncomputable def SL (i x : Nat) : Nat := wEval KLr (List.getD sWordsK i List.nil) x

@[expose] noncomputable def LP (l x : Nat) : Nat := r32 LT (Nat.add (Nat.mul l (nat_lit 20520)) x)

@[expose] noncomputable def ABr (l x : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), r32 TA x, nIf(Nat.beq l (nat_lit 1), r32 J3K.AI x,
    nIf(Nat.beq l (nat_lit 2), r32 TB x, r32 J3K.BI x)))

@[expose] noncomputable def CW (j : Nat) : List Int := List.getD conjWordsAB (r32 CI j) List.nil

@[expose] noncomputable def XK : Nat := nat_lit 50

theorem kl0 : Nat.beq K0 (pmk 20520 15 (KLr 0)) = true := by quickRfl

theorem kl1 : Nat.beq KI0 (pmk 20520 15 (KLr 1)) = true := by quickRfl

theorem kl2 : Nat.beq K1 (pmk 20520 15 (KLr 2)) = true := by quickRfl

theorem kl3 : Nat.beq KI1 (pmk 20520 15 (KLr 3)) = true := by quickRfl

theorem comm0 :
    Nat.beq (pcomp 20520 15 (mask 15) K0 A) (pcomp 20520 15 (mask 15) A K0) = true := by
  quickRfl

theorem comm1 :
    Nat.beq (pcomp 20520 15 (mask 15) K1 A) (pcomp 20520 15 (mask 15) A K1) = true := by
  quickRfl

theorem fix120 : Nat.beq (fixCnt 20520 (r32 TA)) 120 = true := by quickRfl

theorem cent16 :
    centOK LP CT0.PTS CT0.PAR CT0.LAB CT0.cnt CT1.PTS CT1.PAR CT1.LAB CT1.cnt (r32 TA) XK 1 16 =
      true := by
  quickRfl

theorem tkHd : tbfsHdK 20520 0 TK.cnt TK.PTS TK.POS TK.PAR TK.LAB = true := by quickRfl

theorem tkPt :
    allN TK.cnt (tbfsPtK 20520 TK.cnt 4 KLr (fun t => t) TK.PTS TK.POS TK.PAR TK.LAB TK.TI) =
      true := by
  quickRfl

theorem tkCnt : Nat.beq TK.cnt 1920 = true := by quickRfl

theorem tuHd : tbfsHdK 20520 0 TU.cnt TU.PTS TU.POS TU.PAR TU.LAB = true := by quickRfl

theorem tuPt :
    allN TU.cnt (tbfsPtK 20520 TU.cnt 4 UL (fun t => t) TU.PTS TU.POS TU.PAR TU.LAB TU.TI) =
      true := by
  quickRfl

theorem tuCnt : Nat.beq TU.cnt 32 = true := by quickRfl

theorem tsHd : tbfsHdK 20520 0 TS.cnt TS.PTS TS.POS TS.PAR TS.LAB = true := by quickRfl

theorem tsPt :
    allN TS.cnt (tbfsPtK 20520 TS.cnt 4 SL (fun t => t) TS.PTS TS.POS TS.PAR TS.LAB TS.TI) =
      true := by
  quickRfl

theorem tsCnt : Nat.beq TS.cnt 128 = true := by quickRfl

theorem normU : normK KLr 2 UL 4 TU.POS TU.cnt 20520 0 = true := by quickRfl

theorem centU : centUK KLr TK.PTS TK.PAR TK.LAB TK.cnt UL 4 TU.POS TU.cnt 0 = true := by quickRfl

theorem cover : coverK SL TS.PTS TS.PAR TS.LAB TS.cnt ABr 0 CW 0 1 = true := by quickRfl

end CertificateChecks.KernelSpor.J3C

end
