module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelTitsOver.Three

meta def s2G : Array (Array Nat) :=
  CFSG.StandardType.TitsOvergroup.sideGens CFSG.StandardType.TitsThree.pairData 2

meta def idT2 : Array Nat := CFSG.PSL3Four.Native.idTab 1755

end CertificateChecks.KernelTitsOver.Three

public section

#kpenum CertificateChecks.KernelTitsOver.Three.S2E 1755 11 false CertificateChecks.KernelTitsOver.Three.s2G
  CertificateChecks.KernelTitsOver.Three.s2G CertificateChecks.KernelTitsOver.Three.idT2 11232

end
