module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Monster.GMS.Griess13.ChecksGlueInputs
public meta import Certificates.Kernel.Griess13.Gen
public import Certificates.Kernel.Griess13.Gen

public section

namespace CertificateChecks.KernelG13

open CFSG.KC.Eval CFSG.Monster.GMS.Griess13.Co1Data

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
    (`E, natL (eqsOf xRows).toList)]

end CertificateChecks.KernelG13

end
