module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelTitsOver.Three

meta def s3G : Array (Array Nat) :=
  CFSG.StandardType.TitsOvergroup.sideGens CFSG.StandardType.TitsThree.pairData 3

meta def idT3 : Array Nat := CFSG.PSL3Four.Native.idTab 1755

end CertificateChecks.KernelTitsOver.Three

public section

#kpenum CertificateChecks.KernelTitsOver.Three.S3E 1755 11 false CertificateChecks.KernelTitsOver.Three.s3G
  CertificateChecks.KernelTitsOver.Three.s3G CertificateChecks.KernelTitsOver.Three.idT3 11232

end
