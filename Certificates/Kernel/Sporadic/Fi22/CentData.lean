module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData

public section

namespace CertificateChecks.KernelSpor.Fi22CentE

open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.Sporadic.FischerOddCore.Native

meta def eM : Array (Array Nat) := centClosure.1

meta def keyM : Array Nat := eM.map (keyAt 3510 fivePts)

meta def tabsM : Array (Array Nat) :=
  #[centClosure.2.1, centClosure.2.2.1, centClosure.2.2.2,
    (List.range eM.size).toArray.qsort fun a b => keyM[a]! < keyM[b]!]

meta def negM : Array (Array Nat) :=
  #[#[((List.range eM.size).find? fun i => 0 < i &&
    CFSG.Monster.B.Co2.Native.eqA 3510 (CFSG.Sporadic.FischerOddCore.Native.powA 3510 eM[i]! 24)
      (CFSG.Monster.B.Co2.Native.idA 3510)).getD 0]]

end CertificateChecks.KernelSpor.Fi22CentE

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CentE.NEG CertificateChecks.KernelSpor.Fi22CentE.negM 10
#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CentE.EK CertificateChecks.KernelSpor.Fi22CentE.eM 12
#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CentE.TB CertificateChecks.KernelSpor.Fi22CentE.tabsM 10

end
