module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcU6Inputs
public import CFSG.Assembly.Defs

public section

namespace CertificateChecks.KernelLC.ExcU6

open CFSG.KC.Eval CFSG.ComponentClassification.RankTwoClassical.ExcU6

public meta def zigU (e : Int) : Nat := if 0 ≤ e then 2 * e.toNat else 2 * (-e).toNat - 1

public meta def encDerivs (ds : List (List (ℕ × List ℤ × ℕ))) : Val :=
  .list (ds.toArray.map fun d => .list (#[Val.list #[]] ++ d.toArray.map fun s =>
    .list ((#[s.1, s.2.2] ++ (s.2.1.map zigU).toArray).map Val.nat)))

public meta def stepU6 (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  .ok #[(`d1, encDerivs (parseDerivs d1Data)), (`d2, encDerivs (parseDerivs d2Data)),
    (`d3, encDerivs (parseDerivs d3Data))]

end CertificateChecks.KernelLC.ExcU6

end
