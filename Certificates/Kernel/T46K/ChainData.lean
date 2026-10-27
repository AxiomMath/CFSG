module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Data.CFSGNative.Fi22.Local
public meta import Certificates.Data.CFSGNative.Fi22.Local

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT46

open CFSG.Sporadic.Fi22.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

meta def lettersM : Array Table := t46Letters ()

meta def lv0M : Array Nat := levelLetters lettersM t46Base 0
meta def lv1M : Array Nat := levelLetters lettersM t46Base 1
meta def lv2M : Array Nat := levelLetters lettersM t46Base 2
meta def lv3M : Array Nat := levelLetters lettersM t46Base 3
meta def lv4M : Array Nat := levelLetters lettersM t46Base 4

end CertificateChecks.KernelT46

#ktbfs CertificateChecks.KernelT46.TT0 693 0 CertificateChecks.KernelT46.lettersM
  CertificateChecks.KernelT46.lv0M
#ktbfs CertificateChecks.KernelT46.TT1 693 1 CertificateChecks.KernelT46.lettersM
  CertificateChecks.KernelT46.lv1M
#ktbfs CertificateChecks.KernelT46.TT2 693 3 CertificateChecks.KernelT46.lettersM
  CertificateChecks.KernelT46.lv2M
#ktbfs CertificateChecks.KernelT46.TT3 693 9 CertificateChecks.KernelT46.lettersM
  CertificateChecks.KernelT46.lv3M
#ktbfs CertificateChecks.KernelT46.TT4 693 45 CertificateChecks.KernelT46.lettersM
  CertificateChecks.KernelT46.lv4M

end
