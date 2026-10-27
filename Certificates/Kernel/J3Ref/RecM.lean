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

meta def mGM : Array (Array Nat) := #[natArr (clsTbl 5), natArr (clsTbl 6)]

meta def ids2M : Array (Array Nat) := idsM 2

meta def mRecM : Array (Array Nat) := recOfM mGM

meta def mHVM : Array (Array Nat) := hvOfM mRecM

meta def mClM : Array Nat := clOfM mRecM mGM

meta def mNpM : Array Nat := conjOfM mRecM (natArr (clsTbl 3))

meta def mQpM : Array Nat :=
  posOfM mRecM #[natArr (j3CentTbl 9), natArr (clsTbl 0), natArr (clsTbl 1), natArr (clsTbl 2)]

end CertificateChecks.KernelJ3Ref

#kmulh CertificateChecks.KernelJ3Ref.J3RM 6156 13 CertificateChecks.KernelJ3Ref.ids2M
  CertificateChecks.KernelJ3Ref.mGM CertificateChecks.KernelJ3Ref.idM 3000

#kmisc_packarrs CertificateChecks.KernelJ3Ref.J3RMV CertificateChecks.KernelJ3Ref.mHVM 64

#krows32 CertificateChecks.KernelJ3Ref.J3RMCl CertificateChecks.KernelJ3Ref.mClM

#krows32 CertificateChecks.KernelJ3Ref.J3RMNp CertificateChecks.KernelJ3Ref.mNpM

#krows32 CertificateChecks.KernelJ3Ref.J3RMQp CertificateChecks.KernelJ3Ref.mQpM

namespace CertificateChecks.KernelJ3Ref

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumB

theorem m_head : bAnd(allN 2 (fun j => bAnd(Nat.beq (J3RM.GI j) (J3ClsP (Nat.add j 5)),
      Nat.beq (J3RM.G j) (pidn 6156 13))),
    bAnd(Nat.beq J3RM.cnt 960, penumHdK (pidn 6156 13) J3RM.cnt 3000 J3RM.T J3RM.PL)) = true := by
  quickRfl

@[expose] noncomputable def mPt (b : Nat) : Bool :=
  allBlk (Nat.mul b 64)
    (penumPtB 6156 13 (mask 13) bsJ J3RM.GI 2 J3RM.cnt J3RM.T J3RM.PL J3RM.POS J3RM.SRT J3RM.SRI) 64

#kc_each CertificateChecks.KernelJ3Ref.mPt 0 15

@[expose] noncomputable def hvM (i : Nat) : Bool := hvK 6156 13 (mask 13) J3RM.T J3RMV i

#kc_each CertificateChecks.KernelJ3Ref.hvM 0 960

@[expose] noncomputable def mHS (b : Nat) : Bool :=
  allBlk (Nat.mul b 64) (hsortVK J3RM.cnt J3RMV J3RM.HS J3RM.HSI) 64

#kc_each CertificateChecks.KernelJ3Ref.mHS 0 15

@[expose] noncomputable def mGJ (j : Nat) : Nat := J3ClsI (Nat.add j 5)

@[expose] noncomputable def mCl (b : Nat) : Bool :=
  allBlk (Nat.mul b 640) (fun c => bIf(Nat.blt c (Nat.mul J3RM.cnt 4),
    findProdB J3RM.cnt 13 (mask 13) bsJ 4 J3RM.T (bothK 2 J3RM.GI mGJ) J3RMCl c, true)) 640

#kc_each CertificateChecks.KernelJ3Ref.mCl 0 6

@[expose] noncomputable def omC (_ : Nat) : Nat := J3ClsP 3

@[expose] noncomputable def omCI (_ : Nat) : Nat := J3ClsI 3

@[expose] noncomputable def mNp (b : Nat) : Bool :=
  allBlk (Nat.mul b 320) (fun c => bIf(Nat.blt c J3RM.cnt,
    findConjB J3RM.cnt 13 (mask 13) bsJ 1 J3RM.T omC omCI J3RMNp c, true)) 320

#kc_each CertificateChecks.KernelJ3Ref.mNp 0 3

theorem m_le : allN 4 (fun j => strictB (r32 J3RMQp j) (fun q => bAnd(Nat.blt q J3RM.cnt,
    agreeC 13 (mask 13) bsJ (J3RM.T q) (tbP j) (pidn 6156 13)))) = true := by
  quickRfl

end CertificateChecks.KernelJ3Ref

end
