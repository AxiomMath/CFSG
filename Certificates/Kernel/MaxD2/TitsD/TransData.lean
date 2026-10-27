module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
meta import Certificates.Data.Kernel.MaxD2.GenTrans
meta import Certificates.Data.TitsFiveLocal
import Certificates.Data.Kernel.MaxD2.Gen
import Certificates.Data.Kernel.MaxD2.GenTrans
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelMaxD2.TitsD

open CFSG.KS.MaxD2 Certificates.MaxD2Perm

meta def preT : Gen.Pre := Gen.pre titsDData 11

meta def invM : Array Nat := Gen.invIdx titsDData preT
meta def cjM : Array Nat := Gen.conjIdx titsDData preT
meta def ncM : Array Nat := Gen.nonCommPair titsDData preT

end CertificateChecks.KernelMaxD2.TitsD

public section

#krows CertificateChecks.KernelMaxD2.TitsD.INV CertificateChecks.KernelMaxD2.TitsD.invM
#krows CertificateChecks.KernelMaxD2.TitsD.CJ CertificateChecks.KernelMaxD2.TitsD.cjM
#krows CertificateChecks.KernelMaxD2.TitsD.NC CertificateChecks.KernelMaxD2.TitsD.ncM

end
