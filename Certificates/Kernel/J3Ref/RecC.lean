module

public import Certificates.Kernel.J3Ref.Bind
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.LocalQT.PEnumD
public import CFSG.Certificates.Kernel.Common.Each
public import Certificates.Data.Kernel.Spor.PEnumB
public import Certificates.Data.Kernel.Spor.MulHQ
meta import Certificates.Data.J3Cls
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3Ref

open CFSG.SectionRank.QTK.Insp443.J3Cls CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def cGM : Array (Array Nat) := (List.range 5).toArray.map fun k => natArr (j3CentTbl (10 + k))

meta def ids5M : Array (Array Nat) := idsM 5

meta def cRecM : Array (Array Nat) := recOfM cGM

meta def cHVM : Array (Array Nat) := hvOfM cRecM

meta def cClM : Array Nat := clOfM cRecM cGM

end CertificateChecks.KernelJ3Ref

#kmulh CertificateChecks.KernelJ3Ref.J3RC 6156 13 CertificateChecks.KernelJ3Ref.ids5M
  CertificateChecks.KernelJ3Ref.cGM CertificateChecks.KernelJ3Ref.idM 3000

#kmisc_packarrs CertificateChecks.KernelJ3Ref.J3RCV CertificateChecks.KernelJ3Ref.cHVM 64

#krows32 CertificateChecks.KernelJ3Ref.J3RCCl CertificateChecks.KernelJ3Ref.cClM

namespace CertificateChecks.KernelJ3Ref

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumB
open CertificateChecks.KernelSpor

theorem c_head : bAnd(allN 5 (fun j => bAnd(Nat.beq (J3RC.GI j) (J3CentP (Nat.add j 10)),
      Nat.beq (J3RC.G j) (pidn 6156 13))),
    bAnd(Nat.beq J3RC.cnt 1920, penumHdK (pidn 6156 13) J3RC.cnt 3000 J3RC.T J3RC.PL)) = true := by
  quickRfl

@[expose] noncomputable def cPt (b : Nat) : Bool :=
  allBlk (Nat.mul b 64)
    (penumPtB 6156 13 (mask 13) bsJ J3RC.GI 5 J3RC.cnt J3RC.T J3RC.PL J3RC.POS J3RC.SRT J3RC.SRI) 64

#kc_each CertificateChecks.KernelJ3Ref.cPt 0 30

@[expose] noncomputable def hvC (i : Nat) : Bool := hvK 6156 13 (mask 13) J3RC.T J3RCV i

#kc_each CertificateChecks.KernelJ3Ref.hvC 0 1920

@[expose] noncomputable def cHS (b : Nat) : Bool :=
  allBlk (Nat.mul b 64) (hsortVK J3RC.cnt J3RCV J3RC.HS J3RC.HSI) 64

#kc_each CertificateChecks.KernelJ3Ref.cHS 0 30

@[expose] noncomputable def cGJ (j : Nat) : Nat := J3CentI (Nat.add j 10)

@[expose] noncomputable def cCl (b : Nat) : Bool :=
  allBlk (Nat.mul b 640) (fun c => bIf(Nat.blt c (Nat.mul J3RC.cnt 10),
    findProdB J3RC.cnt 13 (mask 13) bsJ 10 J3RC.T (bothK 5 J3RC.GI cGJ) J3RCCl c, true)) 640

#kc_each CertificateChecks.KernelJ3Ref.cCl 0 30

theorem c_cent :
    Nat.beq (cntBelowK J3RC.cnt (fun i => centB 13 (mask 13) bsJ ebL (J3RC.T i)) 30) 16 = true := by
  quickRfl

theorem c_norm :
    Nat.beq (cntBelowK J3RC.cnt (fun i => normB 13 (mask 13) bsJ ebL (J3RC.T i)) 30) 192 = true := by
  quickRfl

end CertificateChecks.KernelJ3Ref

end
