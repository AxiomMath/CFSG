module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Monster.GMS.Griess13.ChecksGlueInputs
public meta import Certificates.Kernel.Griess13.Gen
public import Certificates.Kernel.Griess13.Gen

public section

namespace CertificateChecks.KernelG13

open CFSG.KC.Eval CFSG.Monster.GMS.Griess13.Co1Data

public meta def packs4 : List Nat → List Nat
  | e0 :: e1 :: e2 :: e3 :: E =>
    let c (s : Nat) : Nat := (if s.testBit 0 then e0 else 0) ^^^ (if s.testBit 1 then e1 else 0) ^^^
      (if s.testBit 2 then e2 else 0) ^^^ (if s.testBit 3 then e3 else 0)
    (List.range 16).foldl (fun P s => P ||| (c s <<< (576 * s))) 0 :: packs4 E
  | _ => []

public meta def stepGlue (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let p2 := parseSLP slpMax2
  let pab := parseSLP slpWordsAB
  .ok #[(`s2L, .list (p2.lines.toArray.map fun l => .list (#[Val.nat l.1] ++ encFacts l.2))),
    (`s2O, .list (encFacts p2.outs)),
    (`sabL, .list (pab.lines.toArray.map fun l => .list (#[Val.nat l.1] ++ encFacts l.2))),
    (`sabO, .list (encFacts pab.outs)),
    (`H, natL (prHout.map packPR)),
    (`G, .nat (packPR prG)),
    (`X, natL ((List.finRange 3).map fun k => packPR (prX k))),
    (`Y, natL ((List.finRange 3).map fun k => packPR (prY k))),
    (`AB, natL (prAB.map packPR)),
    (`T, natL ((List.range 8).map fun i => packRows (trows i))),
    (`E, natL (eqsOf xRows).toList),
    (`P, natL (packs4 (eqsOf xRows).toList))]

end CertificateChecks.KernelG13

end
