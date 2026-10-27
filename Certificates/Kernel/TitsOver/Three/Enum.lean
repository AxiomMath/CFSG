module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelTitsOver.Three

meta def pG : Array (Array Nat) :=
  CFSG.StandardType.TitsOvergroup.pGens CFSG.StandardType.TitsThree.pairData

meta def nG : Array (Array Nat) :=
  CFSG.StandardType.TitsOvergroup.nGens CFSG.StandardType.TitsThree.pairData

meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 1755

end CertificateChecks.KernelTitsOver.Three

public section

#kpenum CertificateChecks.KernelTitsOver.Three.PE 1755 11 false CertificateChecks.KernelTitsOver.Three.pG
  CertificateChecks.KernelTitsOver.Three.pG CertificateChecks.KernelTitsOver.Three.idT 27

#kpenum CertificateChecks.KernelTitsOver.Three.NE 1755 11 false CertificateChecks.KernelTitsOver.Three.nG
  CertificateChecks.KernelTitsOver.Three.nG CertificateChecks.KernelTitsOver.Three.idT 216

end
