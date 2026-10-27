module

public import Certificates.Kernel.Th.Fam.K
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ThCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Th.Max3.AllConjInputs
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.InvolutionsBase1
public import CFSG.Sporadic.Th.Max3.InvolutionsInputs
public import CFSG.Sporadic.Th.Max3.QuotientBase1
public import CFSG.Sporadic.Th.Max3.QuotientInputs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Max3.AllConj
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

@[expose] def dihT : TE := .mul .a (.mul (.mul (.ab thDihWord) .a) (.ab (invWord thDihWord)))

theorem ok129003 : (Nat.beq ((TE.pow dihT 19).pk thK) (TE.one.pk thK) &&
    !Nat.beq (dihT.pk thK) (TE.one.pk thK)) = true := by quickRfl

end CertificateChecks.KernelTh.Fam

end
