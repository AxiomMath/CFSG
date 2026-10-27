module

public import Certificates.Kernel.HeLoc.TreeCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
public meta import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib
public import Mathlib

public section

namespace CertificateChecks.KernelRuThree

open CFSG.EvenSporadicStandard.RuStd.S2

meta def frM : List Nat :=
  (List.range 7).map fun i =>
    match ruThreeRels.find? (fun r => r.2.1 == i && decide (r.1 < i)) with
    | some r => 8 * r.1 + r.2.2 + 1
    | none => 0

meta def cgM : Array (Array Nat) := ruThreeC0Gens

end CertificateChecks.KernelRuThree

#kmisc_packarrs CertificateChecks.KernelRuThree.CG CertificateChecks.KernelRuThree.cgM 12
#kh_tree CertificateChecks.KernelRuThree.C0 CFSG.EvenSporadicStandard.RuStd.S2.ruThreeC0Cert 4060
  CFSG.EvenSporadicStandard.RuStd.S2.ruThreeKeys
#knatlist CertificateChecks.KernelRuThree.FR CertificateChecks.KernelRuThree.frM

end
