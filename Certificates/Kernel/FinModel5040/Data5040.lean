module

public import Certificates.Data.Kernel.Misc.A7Nat
import CFSG.Certificates.Kernel.Spor.PackWord
meta import CFSG.GH74.GLS.C3.Layer2.FinModelFactsDataInputs
meta import CFSG.Certificates.Kernel.LocalQTPermSound
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
meta import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Positivity.Finset

namespace CertificateChecks.KernelFM5040

open CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.Model.Facts CFSG.KC.LQT.P

meta def mS (n : Nat) [NeZero n] : List Nat :=
  [code (a0perm n), code (emb n (x0 n)), code (gensPair n).1, code (gensPair n).2]

meta def rS (n : Nat) [NeZero n] : List Nat := (Rl n).map code

meta def sS (n : Nat) [NeZero n] : List Nat := (Sl n).map code

meta def cS (n : Nat) [NeZero n] : List Nat := (Cl n).map code

meta def mS6 : List Nat := mS 6
meta def rS6 : List Nat := rS 6
meta def sS6 : List Nat := sS 6
meta def cS6 : List Nat := cS 6
meta def mS7 : List Nat := mS 7
meta def rS7 : List Nat := rS 7
meta def sS7 : List Nat := sS 7
meta def cS7 : List Nat := cS 7

end CertificateChecks.KernelFM5040

public section

open CertificateChecks.KernelFM5040

#knatlist CertificateChecks.KernelFM5040.M6 mS6
#knatlist CertificateChecks.KernelFM5040.R6 rS6
#knatlist CertificateChecks.KernelFM5040.S6 sS6
#knatlist CertificateChecks.KernelFM5040.C6 cS6
#knatlist CertificateChecks.KernelFM5040.M7 mS7
#knatlist CertificateChecks.KernelFM5040.R7 rS7
#knatlist CertificateChecks.KernelFM5040.S7 sS7
#knatlist CertificateChecks.KernelFM5040.C7 cS7

end
