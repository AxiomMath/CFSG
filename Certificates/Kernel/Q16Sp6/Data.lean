module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Sporadic.OrbRecGen
public import CFSG.Certificates.Kernel.Common.Eval
public import Certificates.Data.Kernel.Q16BK
meta import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Kernel.LocalComp.Q16Wit
meta import CFSG.Sporadic.Schreier.Co3Arrays
meta import Certificates.Kernel.Sporadic.RawGen

namespace CertificateChecks.KernelQ16Sp6.E

open CFSG.Sporadic.Schreier.Co3 CFSG.KS.RawGen CFSG.KC.Q16Wit

meta def wordsM : List (List Nat) := [[0], [1], [2], [3], [4], [5], [9, 7], [11, 7], [19, 15]]

meta def gQ : List (Array Nat) :=
  wordsM.map fun wd => wd.foldl (fun acc l => comp 36 acc co3Sp36Arrs[l]!) (Array.range 36)

meta def wQ : Array (Array Nat) := q16Trees 36 6 gQ [4, 0, 2]
meta def qSKT : Array Nat := wQ[0]!
meta def qRI : Array Nat := wQ[1]!
meta def qC : Array Nat := wQ[2]!
meta def qW : Array Nat := wQ[3]!
meta def qStep : CFSG.KC.Eval.Step := q16Step 36 6 gQ [4, 0, 2]

end CertificateChecks.KernelQ16Sp6.E

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelQ16Sp6.CS CertificateChecks.KernelQ16Sp6.E.gQ 36 6
#kc_eval CertificateChecks.KernelQ16Sp6 CS CertificateChecks.KernelQ16Sp6.E.qStep
#kc_nattree CertificateChecks.KernelQ16Sp6.CS.SKT CertificateChecks.KernelQ16Sp6.E.qSKT
#kc_nattree CertificateChecks.KernelQ16Sp6.CS.RI CertificateChecks.KernelQ16Sp6.E.qRI
#kc_nattree CertificateChecks.KernelQ16Sp6.CS.C CertificateChecks.KernelQ16Sp6.E.qC
#kc_nattree CertificateChecks.KernelQ16Sp6.CS.W CertificateChecks.KernelQ16Sp6.E.qW

end
