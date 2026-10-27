module

public import Certificates.Kernel.L34W.Outer
public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Data.Kernel.L34W.OutCov
public import Certificates.Data.Kernel.Spor.PEnum
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.L34W.OutCovData

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kmisc_packarrs CertificateChecks.KernelL34W.OC.H CertificateChecks.KernelL34W.hdrArr 16
#kmisc_packarrs CertificateChecks.KernelL34W.OC.FK CertificateChecks.KernelL34W.fkArr 6
#kmisc_packarrs CertificateChecks.KernelL34W.OC.FT CertificateChecks.KernelL34W.ftArr 6
#kmisc_packarrs CertificateChecks.KernelL34W.OC.LT CertificateChecks.KernelL34W.ltArr 12
#kmisc_packarrs CertificateChecks.KernelL34W.OC.S3 CertificateChecks.KernelL34W.s3Arr 32
#kmisc_packarrs CertificateChecks.KernelL34W.OC.WB CertificateChecks.KernelL34W.wbArr 10
#kmisc_packarrs CertificateChecks.KernelL34W.OC.V CertificateChecks.KernelL34W.vArr 10
#kmisc_packarrs CertificateChecks.KernelL34W.OC.K CertificateChecks.KernelL34W.kapArr 16

#kpenum CertificateChecks.KernelL34W.OCE0 42 6 false CertificateChecks.KernelL34W.ebG0
  CertificateChecks.KernelL34W.ebG0 CertificateChecks.KernelL34W.id42 64
#kpenum CertificateChecks.KernelL34W.OCE2 42 6 false CertificateChecks.KernelL34W.ebG2
  CertificateChecks.KernelL34W.ebG2 CertificateChecks.KernelL34W.id42 64
#kpenum CertificateChecks.KernelL34W.OCE4 42 6 false CertificateChecks.KernelL34W.ebG4
  CertificateChecks.KernelL34W.ebG4 CertificateChecks.KernelL34W.id42 64
#kpenum CertificateChecks.KernelL34W.OCE5 42 6 false CertificateChecks.KernelL34W.ebG5
  CertificateChecks.KernelL34W.ebG5 CertificateChecks.KernelL34W.id42 64
#kpenum CertificateChecks.KernelL34W.OCE6 42 6 false CertificateChecks.KernelL34W.ebG6
  CertificateChecks.KernelL34W.ebG6 CertificateChecks.KernelL34W.id42 64

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KC.L34W CertificateChecks.KernelLC
open CertificateChecks.KernelLC.L34X

@[expose] noncomputable def ocK (c : Nat) (G : Nat → Nat) (k : Nat) (E : Nat → Nat) (cnt : Nat) :
    Bool :=
  caseK YT L34S.T T1X.F AlX.F GT G E (OC.H c) (OC.FK c) (OC.FT c) (OC.LT c) (OC.S3 c) (OC.WB c)
    (OC.V c) cnt k

theorem ch22971c_0 : ocK 0 OCE0.G OCE0.k OCE0.T OCE0.cnt = true := by decide +kernel
theorem ch22971c_1 : ocK 1 OCE0.G OCE0.k OCE0.T OCE0.cnt = true := by decide +kernel
theorem ch22971c_2 : ocK 2 OCE2.G OCE2.k OCE2.T OCE2.cnt = true := by decide +kernel
theorem ch22971c_3 : ocK 3 OCE2.G OCE2.k OCE2.T OCE2.cnt = true := by decide +kernel
theorem ch22971c_4 : ocK 4 OCE4.G OCE4.k OCE4.T OCE4.cnt = true := by decide +kernel
theorem ch22971c_5 : ocK 5 OCE5.G OCE5.k OCE5.T OCE5.cnt = true := by decide +kernel
theorem ch22971c_6 : ocK 6 OCE6.G OCE6.k OCE6.T OCE6.cnt = true := by decide +kernel
theorem ch22971c_7 : ocK 7 OCE4.G OCE4.k OCE4.T OCE4.cnt = true := by decide +kernel
theorem ch22971c_8 : ocK 8 OCE5.G OCE5.k OCE5.T OCE5.cnt = true := by decide +kernel
theorem ch22971c_9 : ocK 9 OCE6.G OCE6.k OCE6.T OCE6.cnt = true := by decide +kernel

theorem ch22971g_inv : invOKK T1X.F = true := by decide +kernel

theorem ch22971g_match : matchOK YT RP = true := by decide +kernel

theorem ch22971g_kap : kapOK AlX.F OC.K = true := by decide +kernel

@[expose] noncomputable def ocE (G : Nat → Nat) (k cnt : Nat) (T PL POS SRT SRI : Nat → Nat) : Bool :=
  bAnd(penumHdK (pidn 42 6) cnt 64 T PL,
    allN cnt (penumPtK 42 6 (mask 6) (42 * 6) false G G k cnt T PL POS SRT SRI))

theorem ch22971e_0 : ocE OCE0.G OCE0.k OCE0.cnt OCE0.T OCE0.PL OCE0.POS OCE0.SRT OCE0.SRI = true := by
  decide +kernel
theorem ch22971e_2 : ocE OCE2.G OCE2.k OCE2.cnt OCE2.T OCE2.PL OCE2.POS OCE2.SRT OCE2.SRI = true := by
  decide +kernel
theorem ch22971e_4 : ocE OCE4.G OCE4.k OCE4.cnt OCE4.T OCE4.PL OCE4.POS OCE4.SRT OCE4.SRI = true := by
  decide +kernel
theorem ch22971e_5 : ocE OCE5.G OCE5.k OCE5.cnt OCE5.T OCE5.PL OCE5.POS OCE5.SRT OCE5.SRI = true := by
  decide +kernel
theorem ch22971e_6 : ocE OCE6.G OCE6.k OCE6.cnt OCE6.T OCE6.PL OCE6.POS OCE6.SRT OCE6.SRI = true := by
  decide +kernel

theorem ch22971n_s3 : (!c3K YT L34S.T (YT 64) (OC.FT 0) 8 (Nat.xor (OC.S3 0) (Nat.shiftLeft 1 (32 + 13)))
    4) = true := by decide +kernel

theorem ch22971n_wa : (!c4AK YT T1X.F AlX.F OCE0.T OCE0.cnt 4369 (OC.LT 0) 32 16) = true := by
  decide +kernel

theorem ch22971n_wb : (!c4BK YT T1X.F AlX.F OCE2.T OCE2.cnt 4369 (YT 128) (OC.FT 2) 4 (OC.LT 2) 48
    0) = true := by decide +kernel

theorem ch22971n_v : (!c5K T1X.F AlX.F 4369 1 0) = true := by decide +kernel

theorem ch22971n_l : (!lOK YT AlX.F 1 0 4369 (YT 64) (Nat.shiftRight (OC.LT 0) 12) 31) = true := by
  decide +kernel

theorem ch22971n_f : (!fixOK T1X.F AlX.F 4369 1 (Nat.xor (OC.FK 0) 1) 8) = true := by decide +kernel

theorem ch22971n_m : (!matchOK YT (patchT RP 2 (RP 1))) = true := by decide +kernel

theorem ch22971n_k : (!kapOK AlX.F (patchT OC.K 0 (Nat.xor (OC.K 0) (Nat.shiftLeft 7 48)))) = true := by
  decide +kernel

theorem ch22971n_i : (!invOKK (patchT T1X.F 0 (Nat.lor (T1X.F 0) (Nat.shiftLeft 1 6)))) = true := by
  decide +kernel

end CertificateChecks.KernelL34W

end
