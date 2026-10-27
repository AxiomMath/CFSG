module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.Kernel.SmithEKF

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval

meta def val1 (l : List Nat) : Val := .list (l.toArray.map .nat)

meta def val2 (l : List (List Nat)) : Val := .list (l.toArray.map val1)

meta def val3 (l : List (List (List Nat))) : Val := .list (l.toArray.map val2)

meta def val4 (l : List (List (List (List Nat)))) : Val := .list (l.toArray.map val3)

public meta def tabStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "tabStep: expected no arguments"
  return #[(`L, val4 CFSG.SmithE.K.cTabQ)]

end CertificateChecks.KernelSmithEK
