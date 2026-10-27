module

public import Certificates.Kernel.Sporadic.OddCore.HND0
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.HNOddCore.QCheckInputs
meta import CFSG.Sporadic.HNOddCore.QCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2089

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore.InvData

meta def sM : Array (Array Nat) := s4Perms
meta def qM : Array (Array Nat) := qPerms
meta def bM : Array (Array Nat) := qbList 800 qPerms
meta def kM : Array (Array Nat) := colPerms
meta def cvS : Array (Array Nat) := strongArrs 800 (cvGens s4Perms) QData.cvWords
meta def qS : Array (Array Nat) := strongArrs 800 qPerms QData.qWords
meta def kS : Array (Array Nat) := strongArrs 256 colPerms QData.conjWords
meta def cvBA : Array Nat := (QData.cvBase.map Fin.val).toArray
meta def qBA : Array Nat := (QData.qBase.map Fin.val).toArray
meta def kBA : Array Nat := (QData.conjBase.map Fin.val).toArray
@[expose] def cvD : List (List Int) := (QData.cvWords.extract 10 QData.cvWords.size).toList
@[expose] def qD : List (List Int) := (QData.qWords.extract 8 QData.qWords.size).toList
@[expose] def kD : List (List Int) := (QData.conjWords.extract 11 QData.conjWords.size).toList

end CertificateChecks.KernelSpor.HN2089

#kmisc_packarrs CertificateChecks.KernelSpor.HQS CertificateChecks.KernelSpor.HN2089.sM 10
#kmisc_packarrs CertificateChecks.KernelSpor.HQQ CertificateChecks.KernelSpor.HN2089.qM 10
#kmisc_packarrs CertificateChecks.KernelSpor.HQB CertificateChecks.KernelSpor.HN2089.bM 10
#kmisc_packarrs CertificateChecks.KernelSpor.HQK CertificateChecks.KernelSpor.HN2089.kM 9

#ks_rawchain CertificateChecks.KernelSpor.HQCV 800 10 64 CertificateChecks.KernelSpor.HN2089.cvS
  CertificateChecks.KernelSpor.HN2089.cvBA 10 CertificateChecks.KernelSpor.HN2089.cvD
#ks_rawchain CertificateChecks.KernelSpor.HQQC 800 10 64 CertificateChecks.KernelSpor.HN2089.qS
  CertificateChecks.KernelSpor.HN2089.qBA 8 CertificateChecks.KernelSpor.HN2089.qD
#ks_rawchain CertificateChecks.KernelSpor.HQKC 256 9 64 CertificateChecks.KernelSpor.HN2089.kS
  CertificateChecks.KernelSpor.HN2089.kBA 11 CertificateChecks.KernelSpor.HN2089.kD

end
