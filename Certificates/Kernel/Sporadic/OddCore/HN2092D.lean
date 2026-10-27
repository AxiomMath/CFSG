module

public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import Certificates.Kernel.Sporadic.OddCore.BfsLCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.HNOddCore.SixCheckInputs
meta import CFSG.Sporadic.HNOddCore.SixCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2092

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.ONSchreier.Native

meta def gM : Array (Array Nat) := om0Gens
meta def xM : Array (Array Nat) :=
  #[pword 1100 om0Gens (pinvs 1100 om0Gens) SixData.wa,
    pword 1100 om0Gens (pinvs 1100 om0Gens) SixData.wb]
meta def abM : Array (Array Nat) := #[dA om0Gens, dB om0Gens]
meta def sM : Array (Array Nat) := strongArrs 1100 abM SixData.dWords
meta def dBA : Array Nat := dBaseArr
meta def oM : Array Nat := bfsList 1100 abM 0
meta def hM : Array (Array Nat) := dStab (dA om0Gens) (dB om0Gens)
meta def lsM : Array (Array Nat) := subOrbits hM
meta def l0 : Array Nat := lsM[0]!
meta def l1 : Array Nat := lsM[1]!
meta def l2 : Array Nat := lsM[2]!
meta def l3 : Array Nat := lsM[3]!
meta def l4 : Array Nat := lsM[4]!
meta def lbM : Array Nat := subLabels lsM
meta def pnM : Array Nat := Id.run do
  let mut t : Array Nat := Array.replicate 1100 0
  for L in lsM do
    for k in [0:L.size] do
      t := t.set! L[k]! k
  return t
@[expose] def dD : List (List Int) := (SixData.dWords.extract 2 SixData.dWords.size).toList

end CertificateChecks.KernelSpor.HN2092

#kmisc_packarrs CertificateChecks.KernelSpor.HSG CertificateChecks.KernelSpor.HN2092.gM 11
#kmisc_packarrs CertificateChecks.KernelSpor.HSX CertificateChecks.KernelSpor.HN2092.xM 11

#kbfsl CertificateChecks.KernelSpor.HSO 1100 CertificateChecks.KernelSpor.HN2092.abM
  CertificateChecks.KernelSpor.HN2092.oM
#kbfsl CertificateChecks.KernelSpor.HSL0 1100 CertificateChecks.KernelSpor.HN2092.hM
  CertificateChecks.KernelSpor.HN2092.l0
#kbfsl CertificateChecks.KernelSpor.HSL1 1100 CertificateChecks.KernelSpor.HN2092.hM
  CertificateChecks.KernelSpor.HN2092.l1
#kbfsl CertificateChecks.KernelSpor.HSL2 1100 CertificateChecks.KernelSpor.HN2092.hM
  CertificateChecks.KernelSpor.HN2092.l2
#kbfsl CertificateChecks.KernelSpor.HSL3 1100 CertificateChecks.KernelSpor.HN2092.hM
  CertificateChecks.KernelSpor.HN2092.l3
#kbfsl CertificateChecks.KernelSpor.HSL4 1100 CertificateChecks.KernelSpor.HN2092.hM
  CertificateChecks.KernelSpor.HN2092.l4

#krows CertificateChecks.KernelSpor.HSLB CertificateChecks.KernelSpor.HN2092.lbM
#krows CertificateChecks.KernelSpor.HSPN CertificateChecks.KernelSpor.HN2092.pnM

end
