module

public import Certificates.Data.GrSLitL34FactsCF23SuzCheck
public import Certificates.Data.GrSLitL34SuzStdOddCtrlGenCheck
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.Suz.Text2306
meta import Certificates.Data.GrSLitL34FactsCF23SuzCheck

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Suz786001T CFSG.ComponentClassification.GSThmB.CF23L34.suzFusText

#kmisc_hexflat CertificateChecks.KernelSpor.Suz786001T
  CFSG.ComponentClassification.GSThmB.CF23L34.suzFusText 3 1782 11 3

namespace CertificateChecks.KernelSpor.Suz786001

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.GrSLit.L34Sec5S

@[expose] noncomputable def SC (k : Nat) : Nat :=
  [Suz786001T.F 0, Suz786001T.F 1,
    pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) (Suz786001T.F 2) (Suz786001T.F 0))
      (pinvS 1782 11 (mask 11) (Suz786001T.F 2)),
    pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) (Suz786001T.F 2) (Suz786001T.F 1))
      (pinvS 1782 11 (mask 11) (Suz786001T.F 2))].getD k 0

@[expose] noncomputable def SIC (k : Nat) : Nat := pinvS 1782 11 (mask 11) (SC k)

theorem kSz : szOK 1782 11 = true := by decide +kernel

theorem kPermY1 : permB 1782 11 (Suz786001T.F 0) = true := by decide +kernel

theorem kPermY2 : permB 1782 11 (Suz786001T.F 1) = true := by decide +kernel

theorem kPermM : permB 1782 11 (Suz786001T.F 2) = true := by decide +kernel

theorem kLetters0 : lettersOK 4 suzCtrlWordB0 = true := by decide +kernel

theorem kLetters1 : lettersOK 4 suzCtrlWordB1 = true := by decide +kernel

theorem kWord0 :
    Nat.beq (wordK 1782 11 (mask 11) (pidn 1782 11) SC SIC suzCtrlWordB0) Suz2306.B0 = true := by
  decide +kernel

theorem kWord1 :
    Nat.beq (wordK 1782 11 (mask 11) (pidn 1782 11) SC SIC suzCtrlWordB1) Suz2306.B1 = true := by
  decide +kernel

theorem kNegPerm : (!permB 1782 11 (Suz786001T.F 0 + 1)) = true := by decide +kernel

theorem kNegSwap :
    (!Nat.beq (wordK 1782 11 (mask 11) (pidn 1782 11) SC SIC suzCtrlWordB0) Suz2306.B1) = true := by
  decide +kernel

theorem kNegWord :
    (!Nat.beq (wordK 1782 11 (mask 11) (pidn 1782 11) SC SIC (suzCtrlWordB0.drop 1))
      Suz2306.B0) = true := by
  decide +kernel

theorem kNegLetters : (!lettersOK 4 (5 :: suzCtrlWordB0)) = true := by decide +kernel

end CertificateChecks.KernelSpor.Suz786001

end
