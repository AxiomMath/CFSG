module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.IntWordsCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.TabSuzA
public meta import Certificates.Data.TabSuzA
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzA17321

open CFSG.HardMathSupport.Dickson.I271.TabSuzA

meta def sS : Array (Array Nat) := aStrong ()

meta def sBA : Array Nat := aBase

meta def sDM : Array (List Int) := aWords.extract 3 11

end CertificateChecks.KernelSuzA17321

end

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSuzA17321.SAP CFSG.HardMathSupport.Dickson.I271.TabSuzA.hex
#kmisc_hexflat CertificateChecks.KernelSuzA17321.SAP CFSG.HardMathSupport.Dickson.I271.TabSuzA.hex
  3 1782 11 11
#kc_intwords CertificateChecks.KernelSuzA17321.SAD CertificateChecks.KernelSuzA17321.sDM
#ks_rawchain CertificateChecks.KernelSuzA17321.SAC 1782 11 64 CertificateChecks.KernelSuzA17321.sS
  CertificateChecks.KernelSuzA17321.sBA 3 CertificateChecks.KernelSuzA17321.SAD

public section

namespace CertificateChecks.KernelSuzA17321

open CFSG.KC.Enum CFSG.KS

theorem SAC.perm :
    allN 11 (fun j => permOK 1782 11 (mask 11) (1782 * 11) (SAC.S j) (SAC.SI j)) = true := by
  quickRfl

theorem SAC.FS : allN 11 (fun j => Nat.beq (SAP.F j) (SAC.S j)) = true := by quickRfl

end CertificateChecks.KernelSuzA17321

end
