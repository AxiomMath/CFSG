module

public import Certificates.Kernel.J4Q.OrbBase
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.LQT.Syl CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

@[expose] noncomputable def tr6K (i : Nat) : Bool :=
  vtB rm (rep 1 128 1024) [L0, L1, L2] (vptsK rm (repK 6) CH6.flatten) (CH6.getD i [])
    (P06.getD i 0) (1 + 1024 * i)

@[expose] noncomputable def in6K (i : Nat) : Bool :=
  andB (eqLK (sortN ((pchK rm (repK 6) CH6).getD i [])) (SQ6.getD i []))
    (eqLK (diffS (SQ6.getD i []) SPC6.flatten) List.nil)

@[expose] noncomputable def sp6K (i : Nat) : Bool := eqLK (diffAll (SPC6.getD i []) SQ6) List.nil

@[expose] noncomputable def cl6K (i : Nat) : Bool :=
  clB rm (rep 1 128 1024) [L0, L1, L2] ((pchK rm (repK 6) CH6).getD i []) SPC6.flatten

#j4q_all CFSG.KD.J4Q.T6 CertificateChecks.KernelJ4Q.tr6K 28
#j4q_all CFSG.KD.J4Q.I6 CertificateChecks.KernelJ4Q.in6K 29
#j4q_all CFSG.KD.J4Q.S6 CertificateChecks.KernelJ4Q.sp6K 28
#j4q_all CFSG.KD.J4Q.C6 CertificateChecks.KernelJ4Q.cl6K 29

theorem size6 : sizeK 28336 CH6 SPC6 = true := by quickRfl

theorem sinc6 : sincK SPC6.flatten 0 = true := by quickRfl

theorem orb6_vorbOK : vorbOK locTabs rep6Vec orb6 28336 = true :=
  orb_ok (ℓ := 6) (P0 := P06) (SQ := SQ6) (by decide) (by decide) size6 T6.all sinc6 rfl I6.all
    S6.all C6.all

@[expose] noncomputable def tr5K (i : Nat) : Bool :=
  vtB rm (rep 1 128 1024) [L0, L1, L2] (vptsK rm (repK 5) CH5.flatten) (CH5.getD i [])
    (P05.getD i 0) (1 + 1024 * i)

@[expose] noncomputable def in5K (i : Nat) : Bool :=
  andB (eqLK (sortN ((pchK rm (repK 5) CH5).getD i [])) (SQ5.getD i []))
    (eqLK (diffS (SQ5.getD i []) SPC5.flatten) List.nil)

@[expose] noncomputable def sp5K (i : Nat) : Bool := eqLK (diffAll (SPC5.getD i []) SQ5) List.nil

@[expose] noncomputable def cl5K (i : Nat) : Bool :=
  clB rm (rep 1 128 1024) [L0, L1, L2] ((pchK rm (repK 5) CH5).getD i []) SPC5.flatten

#j4q_all CFSG.KD.J4Q.T5 CertificateChecks.KernelJ4Q.tr5K 15
#j4q_all CFSG.KD.J4Q.I5 CertificateChecks.KernelJ4Q.in5K 16
#j4q_all CFSG.KD.J4Q.S5 CertificateChecks.KernelJ4Q.sp5K 15
#j4q_all CFSG.KD.J4Q.C5 CertificateChecks.KernelJ4Q.cl5K 16

theorem size5 : sizeK 15180 CH5 SPC5 = true := by quickRfl

theorem sinc5 : sincK SPC5.flatten 0 = true := by quickRfl

theorem orb5_vorbOK : vorbOK locTabs rep5Vec orb5 15180 = true :=
  orb_ok (ℓ := 5) (P0 := P05) (SQ := SQ5) (by decide) (by decide) size5 T5.all sinc5 rfl I5.all
    S5.all C5.all

end CertificateChecks.KernelJ4Q

end
