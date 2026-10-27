module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroupData
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelTitsOver.Five

meta def crG : Array (Array Nat) :=
  Certificates.MaxD2Perm.rGens (CFSG.StandardType.TitsFive.lLocalData ())

meta def cnG : Array (Array Nat) :=
  Certificates.MaxD2Perm.nGens (CFSG.StandardType.TitsFive.lLocalData ())

meta def cidT : Array Nat := CFSG.PSL3Four.Native.idTab 1755

end CertificateChecks.KernelTitsOver.Five

public section

#kpenum CertificateChecks.KernelTitsOver.Five.CRE 1755 11 false CertificateChecks.KernelTitsOver.Five.crG
  CertificateChecks.KernelTitsOver.Five.crG CertificateChecks.KernelTitsOver.Five.cidT 25

#kpenum CertificateChecks.KernelTitsOver.Five.CNE 1755 11 false CertificateChecks.KernelTitsOver.Five.cnG
  CertificateChecks.KernelTitsOver.Five.cnG CertificateChecks.KernelTitsOver.Five.cidT 300

end
