module

public import Init
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.LocalComp.FactsVMeta
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreFi24SevenData
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs
import Certificates.Kernel.LocalComp.FactsVMeta

namespace CertificateChecks.KernelMC.F24C

open CFSG.AGLEmbedding.R3 CFSG.KC.LocalComp.FactsVMeta

meta def targets : Array (Array Nat) :=
  targetsA CoreFi247.nregs CoreFi247.prog CoreFi247.prog.length

meta def finA : Array (Array Nat) := finalsA CoreFi247.nregs CoreFi247.prog (CoreFi247.cutA - 2)

meta def finB : Array (Array Nat) := finalsA CoreFi247.nregs CoreFi247.prog (CoreFi247.cutB - 2)

meta def finC : Array (Array Nat) := finalsA CoreFi247.nregs CoreFi247.prog CoreFi247.prog.length

meta def hints : Array (Array Nat) := hintsA CoreFi247.nregs CoreFi247.prog CoreFi247.spec.facts

end CertificateChecks.KernelMC.F24C

#kmisc_packarrs CertificateChecks.KernelMC.F24C.TT CertificateChecks.KernelMC.F24C.targets 20
#kmisc_packarrs CertificateChecks.KernelMC.F24C.RA CertificateChecks.KernelMC.F24C.finA 20
#kmisc_packarrs CertificateChecks.KernelMC.F24C.RB CertificateChecks.KernelMC.F24C.finB 20
#kmisc_packarrs CertificateChecks.KernelMC.F24C.RC CertificateChecks.KernelMC.F24C.finC 20
#kmisc_packarrs CertificateChecks.KernelMC.F24C.HH CertificateChecks.KernelMC.F24C.hints 20
