module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import Certificates.Data.TitsFiveLocal
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelMaxD2.TitsA

meta def rG : Array (Array Nat) := Certificates.MaxD2Perm.rGens Certificates.MaxD2Perm.titsAData

meta def nG : Array (Array Nat) := Certificates.MaxD2Perm.nGens Certificates.MaxD2Perm.titsAData

meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 1755

end CertificateChecks.KernelMaxD2.TitsA

public section

#kpenum CertificateChecks.KernelMaxD2.TitsA.RE 1755 11 false CertificateChecks.KernelMaxD2.TitsA.rG
  CertificateChecks.KernelMaxD2.TitsA.rG CertificateChecks.KernelMaxD2.TitsA.idT 25

#kpenum CertificateChecks.KernelMaxD2.TitsA.NE 1755 11 false CertificateChecks.KernelMaxD2.TitsA.nG
  CertificateChecks.KernelMaxD2.TitsA.nG CertificateChecks.KernelMaxD2.TitsA.idT 2400

end
