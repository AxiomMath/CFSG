module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.McLFivePairs

namespace CertificateChecks.KernelMcL5Pairs

open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.McLFivePairs

meta def uM : Array Nat := (rGens mclFiveDataP)[0]!
meta def vM : Array Nat := (rGens mclFiveDataP)[1]!
meta def b0M : Array (Array Nat) :=
  pairGens uM vM ((repT mclFiveDataP).getD excIdx (CFSG.PSL3Four.Native.idTab 275))
meta def hkM : Array (Array Nat) := conjTabs (nGens mclFiveDataP) (nGensI mclFiveDataP)
meta def bkM : Array (Array Nat) := (hkM.map (blockGens b0M)).flatten
meta def invs (a : Array (Array Nat)) : Array (Array Nat) := a.map (CFSG.PSL3Four.Native.invTab 275)
meta def rgiM : Array (Array Nat) := invs (rGens mclFiveDataP)
meta def b0iM : Array (Array Nat) := invs b0M
meta def hkiM : Array (Array Nat) := invs hkM
meta def bkiM : Array (Array Nat) := invs bkM

end CertificateChecks.KernelMcL5Pairs

public section

#kmisc_packarrs CertificateChecks.KernelMcL5Pairs.RGI CertificateChecks.KernelMcL5Pairs.rgiM 9
#kmisc_packarrs CertificateChecks.KernelMcL5Pairs.B0 CertificateChecks.KernelMcL5Pairs.b0M 9
#kmisc_packarrs CertificateChecks.KernelMcL5Pairs.B0I CertificateChecks.KernelMcL5Pairs.b0iM 9
#kmisc_packarrs CertificateChecks.KernelMcL5Pairs.HK CertificateChecks.KernelMcL5Pairs.hkM 9
#kmisc_packarrs CertificateChecks.KernelMcL5Pairs.HKI CertificateChecks.KernelMcL5Pairs.hkiM 9
#kmisc_packarrs CertificateChecks.KernelMcL5Pairs.BK CertificateChecks.KernelMcL5Pairs.bkM 9
#kmisc_packarrs CertificateChecks.KernelMcL5Pairs.BKI CertificateChecks.KernelMcL5Pairs.bkiM 9

end
