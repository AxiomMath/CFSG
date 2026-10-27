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

open CFSG.SectionRank.QTK.Insp443.J3Cls CFSG.Sporadic.SmallOddCore.Native

meta def sGM : Array (Array Nat) := #[natArr (clsTbl 7), natArr (clsTbl 8), natArr (clsTbl 9)]

meta def ids3M : Array (Array Nat) := idsM 3

meta def sRecM : Array (Array Nat) := recOfM sGM

meta def sHVM : Array (Array Nat) := hvOfM sRecM

meta def sClM : Array Nat := clOfM sRecM sGM

end CertificateChecks.KernelJ3Ref

#kmulh CertificateChecks.KernelJ3Ref.J3RS 6156 13 CertificateChecks.KernelJ3Ref.ids3M
  CertificateChecks.KernelJ3Ref.sGM CertificateChecks.KernelJ3Ref.idM 3000

#kmisc_packarrs CertificateChecks.KernelJ3Ref.J3RSV CertificateChecks.KernelJ3Ref.sHVM 64

#krows32 CertificateChecks.KernelJ3Ref.J3RSCl CertificateChecks.KernelJ3Ref.sClM

namespace CertificateChecks.KernelJ3Ref

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumB

theorem s_head : bAnd(allN 3 (fun j => bAnd(Nat.beq (J3RS.GI j) (J3ClsP (Nat.add j 7)),
      Nat.beq (J3RS.G j) (pidn 6156 13))),
    bAnd(Nat.beq J3RS.cnt 128, penumHdK (pidn 6156 13) J3RS.cnt 3000 J3RS.T J3RS.PL)) = true := by
  quickRfl

@[expose] noncomputable def sPt (i : Nat) : Bool :=
  penumPtB 6156 13 (mask 13) bsJ J3RS.GI 3 J3RS.cnt J3RS.T J3RS.PL J3RS.POS J3RS.SRT J3RS.SRI i

theorem sE0 : allBlk 0 sPt 32 = true := by quickRfl
theorem sE1 : allBlk 32 sPt 32 = true := by quickRfl
theorem sE2 : allBlk 64 sPt 32 = true := by quickRfl
theorem sE3 : allBlk 96 sPt 32 = true := by quickRfl

@[expose] noncomputable def hvS (i : Nat) : Bool := hvK 6156 13 (mask 13) J3RS.T J3RSV i

#kc_each CertificateChecks.KernelJ3Ref.hvS 0 128

theorem sHV : allBlk 0 (hsortVK J3RS.cnt J3RSV J3RS.HS J3RS.HSI) 128 = true := by quickRfl

@[expose] noncomputable def sGJ (j : Nat) : Nat := J3ClsI (Nat.add j 7)

@[expose] noncomputable def sCl (b : Nat) : Bool :=
  allBlk (Nat.mul b 256) (fun c => bIf(Nat.blt c (Nat.mul J3RS.cnt 6),
    findProdB J3RS.cnt 13 (mask 13) bsJ 6 J3RS.T (bothK 3 J3RS.GI sGJ) J3RSCl c, true)) 256

#kc_each CertificateChecks.KernelJ3Ref.sCl 0 3

end CertificateChecks.KernelJ3Ref

end
