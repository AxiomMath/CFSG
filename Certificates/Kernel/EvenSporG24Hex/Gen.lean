module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelBase
public meta import Certificates.Data.Kernel.EvenSporG24Hex.Defs

public section

namespace CertificateChecks.KernelG24Hex

open CFSG.KC.Eval CFSG.KC.EvenSporG24Hex CFSG.EvenSporadicStandard.G24Model

public meta def natL (xs : List Nat) : Val := .list (xs.toArray.map Val.nat)

public meta def stepG24Hex (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let T := tbl.toList
  let U := (List.range 1365).map fun k => T.getD (2 * k) 0
  let W := (List.range 1365).map fun k => T.getD (2 * k + 1) 0
  let GE := (List.range 16).map fun j => ((T.drop (2730 + 196 * j)).take 196)
  let PG := (List.range 16).map fun j => ((T.drop (5866 + 1365 * j)).take 1365)
  let LC := pk 420 ((List.range 1365).map fun k => pk 28 (codesK (U.getD k 0) (W.getD k 0)))
  .ok #[(`U, natL U), (`W, natL W), (`GE, .list (GE.toArray.map natL)),
    (`PG, .list (PG.toArray.map natL)), (`LC, .nat LC)]

end CertificateChecks.KernelG24Hex

end
