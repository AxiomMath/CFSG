module

public import Certificates.Kernel.Sporadic.OddCore.McLTL
public meta import Certificates.Kernel.Sporadic.OddCore.McLTL
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTL

open CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def pgM : Array (Array Nat) :=
  #[CFSG.Sporadic.Schreier.mclStrongArrs[0]!, CFSG.Sporadic.Schreier.mclStrongArrs[1]!]

meta def pgiM : Array (Array Nat) := pgM.map invM

meta def xM : Array Nat := thM[0]!

meta def recC : Array (Array Nat) :=
  (bfs (fun j t => conjTab 275 pgM[j]! pgiM[j]! t) 2 xM 30800).tabs

meta def rcM : Array (Array Nat) := let hs := hsM recC; recR.map (pbM recC hs)

meta def tcM : Array (Array Nat) := let hs := hsM recC; recT.map (pbM recC hs)

end CertificateChecks.KernelSpor.McLTL

#kmulh CertificateChecks.KernelSpor.McLTC 275 9 CertificateChecks.KernelSpor.McLTL.pgM
  CertificateChecks.KernelSpor.McLTL.pgiM CertificateChecks.KernelSpor.McLTL.xM 30800
#kfind CertificateChecks.KernelSpor.McLTQAC CertificateChecks.KernelSpor.McLTL.recC
  CertificateChecks.KernelSpor.McLTL.agM
#kmisc_packarrs CertificateChecks.KernelSpor.McLTQRC CertificateChecks.KernelSpor.McLTL.rcM 32
#kmisc_packarrs CertificateChecks.KernelSpor.McLTQTC CertificateChecks.KernelSpor.McLTL.tcM 32

end
