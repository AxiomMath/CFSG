module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.TabFi22Small
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CertificateChecks.KernelSpor.Fi22SmallT

meta def uM : Array (Array Nat) :=
  #[CFSG.HardMathSupport.Dickson.I271.TabFi22Small.uArr 0,
    CFSG.HardMathSupport.Dickson.I271.TabFi22Small.uArr 1,
    CFSG.HardMathSupport.Dickson.I271.TabFi22Small.uArr 2]

end CertificateChecks.KernelSpor.Fi22SmallT

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22SmallT.U
  CertificateChecks.KernelSpor.Fi22SmallT.uM 12
