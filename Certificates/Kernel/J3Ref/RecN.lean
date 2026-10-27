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

meta def nGM : Array (Array Nat) := #[natArr (clsTbl 5), natArr (clsTbl 6), natArr (clsTbl 3)]

meta def ids3NM : Array (Array Nat) := idsM 3

meta def nRecM : Array (Array Nat) := recOfM nGM

meta def nHVM : Array (Array Nat) := hvOfM nRecM

meta def nClM : Array Nat := clOfM nRecM nGM

end CertificateChecks.KernelJ3Ref

#kmulh CertificateChecks.KernelJ3Ref.J3RN 6156 13 CertificateChecks.KernelJ3Ref.ids3NM
  CertificateChecks.KernelJ3Ref.nGM CertificateChecks.KernelJ3Ref.idM 3000

#kmisc_packarrs CertificateChecks.KernelJ3Ref.J3RNV CertificateChecks.KernelJ3Ref.nHVM 64

#krows32 CertificateChecks.KernelJ3Ref.J3RNCl CertificateChecks.KernelJ3Ref.nClM

namespace CertificateChecks.KernelJ3Ref

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumB

@[expose] noncomputable def nGP (j : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 2), J3ClsP (Nat.add j (nat_lit 5)), J3ClsP (nat_lit 3))

@[expose] noncomputable def nGJ (j : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 2), J3ClsI (Nat.add j (nat_lit 5)), J3ClsI (nat_lit 3))

theorem n_head : bAnd(allN 3 (fun j => bAnd(Nat.beq (J3RN.GI j) (nGP j),
      Nat.beq (J3RN.G j) (pidn 6156 13))),
    bAnd(Nat.beq J3RN.cnt 2880, penumHdK (pidn 6156 13) J3RN.cnt 3000 J3RN.T J3RN.PL)) = true := by
  quickRfl

@[expose] noncomputable def nPt (b : Nat) : Bool :=
  allBlk (Nat.mul b 64)
    (penumPtB 6156 13 (mask 13) bsJ J3RN.GI 3 J3RN.cnt J3RN.T J3RN.PL J3RN.POS J3RN.SRT J3RN.SRI) 64

#kc_each CertificateChecks.KernelJ3Ref.nPt 0 45

@[expose] noncomputable def hvN (i : Nat) : Bool := hvK 6156 13 (mask 13) J3RN.T J3RNV i

#kc_each CertificateChecks.KernelJ3Ref.hvN 0 2880

@[expose] noncomputable def nHS (b : Nat) : Bool :=
  allBlk (Nat.mul b 64) (hsortVK J3RN.cnt J3RNV J3RN.HS J3RN.HSI) 64

#kc_each CertificateChecks.KernelJ3Ref.nHS 0 45

@[expose] noncomputable def nCl (b : Nat) : Bool :=
  allBlk (Nat.mul b 640) (fun c => bIf(Nat.blt c (Nat.mul J3RN.cnt 6),
    findProdB J3RN.cnt 13 (mask 13) bsJ 6 J3RN.T (bothK 3 J3RN.GI nGJ) J3RNCl c, true)) 640

#kc_each CertificateChecks.KernelJ3Ref.nCl 0 27

end CertificateChecks.KernelJ3Ref

end
