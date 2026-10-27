module

public import Certificates.Data.Kernel.LocalComp.ThreeWP
public import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRuData
import CFSG.Assembly.Defs
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness
meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
meta import CFSG.Sporadic.Schreier.Outer
meta import CFSG.Sporadic.Schreier.RuAutInner

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.RuW

open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th.Native

meta def gensM : Array (Array Nat) :=
  (ruCTab ++ ruCInvTab).map fun t => t.map (·.toNat)

meta def closM : Array Table × Array Nat × Array Nat := conjClosure 4060 ruCTab ruCInvTab ruQTab 400

meta def entM : Array (Array Nat) := closM.1.map fun t => t.map (·.toNat)

meta def rowsM : Array (Array Nat) := Id.run do
  let (E, par, lab) := closM
  let idx := fun (t : Table) => (E.findIdx? fun e => tblEq 4060 e t).getD 0
  return (Array.range E.size).map fun j =>
    #[par[j]!, lab[j]!] ++ ((Array.range 2).foldl (fun acc l =>
      acc ++ #[idx (conjT 4060 ruCTab[l]! ruCInvTab[l]! E[j]!),
        idx (conjT 4060 ruCInvTab[l]! ruCTab[l]! E[j]!)]) #[])

meta def qyM : Array (Array Nat) := #[ruQTab.map (·.toNat), ruYTab.map (·.toNat)]

end CertificateChecks.KernelLC.RuW

#kmisc_packarrs CertificateChecks.KernelLC.RuW.TG CertificateChecks.KernelLC.RuW.gensM 12
#kmisc_packarrs CertificateChecks.KernelLC.RuW.TE CertificateChecks.KernelLC.RuW.entM 12
#kmisc_packarrs CertificateChecks.KernelLC.RuW.TR CertificateChecks.KernelLC.RuW.rowsM 16
#kmisc_packarrs CertificateChecks.KernelLC.RuW.TQY CertificateChecks.KernelLC.RuW.qyM 12

public section

namespace CertificateChecks.KernelLC.RuW

open CFSG.KC.Enum CFSG.KS CFSG.KC.LocalComp.ThreeWP

@[expose] noncomputable def gP (l : Nat) : Nat := TG l

@[expose] noncomputable def giP (l : Nat) : Nat := TG (Nat.add l 2)

@[expose] noncomputable def letP (z : Int) : Nat := if z = 1 then TG 0 else TG 1

@[expose] def qW : List Int :=
  [1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1,
    1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2]

@[expose] def yW : List Int :=
  [2, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1,
    2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1]

end CertificateChecks.KernelLC.RuW
