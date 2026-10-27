module

public import Certificates.Kernel.L34W.Tabs
public import Certificates.Data.Kernel.L34W.ModK
public import Certificates.Data.GrSLitL34Sec5SWIsoCheck
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.L34W.TwoData

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelL34W.TW CertificateChecks.KernelL34W.twoArr 10

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

@[expose] noncomputable def twoOK (T W : Nat → Nat) : Bool :=
  allN (nat_lit 15) fun k => strictB (W k) fun w =>
    twoC T (kbMasks.getD k 0) (pg 10 (mask 10) w 0) (pg 10 (mask 10) w 1) (pg 10 (mask 10) w 2)
      (pg 10 (mask 10) w 3)

theorem two_k : twoOK T1X.F TW = true := by decide +kernel

theorem two_neg : (!twoOK T1X.F (patchT TW 14 (Nat.add (Nat.sub (TW 14)
    (Nat.shiftLeft (pg 10 (mask 10) (TW 14) 1) 10)) (Nat.shiftLeft (pg 10 (mask 10) (TW 14) 0) 10)))) =
    true := by
  decide +kernel

end CertificateChecks.KernelL34W

end
