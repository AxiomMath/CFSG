module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroupData
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelTitsOver.Five

meta def lG : Array (Array Nat) :=
  Certificates.MaxD2Perm.nGens CFSG.StandardType.TitsFive.lMaxData

meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 1755

end CertificateChecks.KernelTitsOver.Five

public section

#kpenum CertificateChecks.KernelTitsOver.Five.LE 1755 11 false CertificateChecks.KernelTitsOver.Five.lG
  CertificateChecks.KernelTitsOver.Five.lG CertificateChecks.KernelTitsOver.Five.idT 7800

end
