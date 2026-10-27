module

public import Certificates.Kernel.Sporadic.ON.GenTab
public import Certificates.Kernel.Sporadic.ON2.GenWords
public meta import CFSG.RankThree.Native.ONThreeInputs
public meta import CFSG.Certificates.NativeSchreierCard
public meta import CFSG.Sporadic.Schreier.ONCheckChain
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.Tactic.NormNum.GCD

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONW

meta def pM : Array Nat :=
  CFSG.ONSchreier.Native.pcomp CFSG.Sporadic.ON.Native.nPts CFSG.RankThree.Native.onThreeYArrs[0]!
    CFSG.RankThree.Native.onThreeYArrs[1]!

meta def uM : Array Nat := CFSG.RankThree.Native.onSevenPow pM 3

meta def wordsM : Array (List Int) := CFSG.RankThree.Native.onThreeY

end CertificateChecks.KernelSpor.ONW

#kon_table CertificateChecks.KernelSpor.ONWT.P CertificateChecks.KernelSpor.ONW.pM
#kon_table CertificateChecks.KernelSpor.ONWT.U CertificateChecks.KernelSpor.ONW.uM
#kon_words CertificateChecks.KernelSpor.ONWW CertificateChecks.KernelSpor.ONW.wordsM

end
