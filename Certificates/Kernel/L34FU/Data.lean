module

public import Certificates.Data.FooteLitL34FUCheck

public section

namespace CertificateChecks.KernelL34FU

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.TBLit.L34FU

@[expose] def fuCode (x : MElt) : Nat := 16 * x.1 + 4 * x.2.1.val + x.2.2.val

@[expose] def fuCell (t i : Nat) : Nat :=
  if candOK t i then
    match allM.find? (fun x => betaRepM 1 x == x && pow4X (mulM x (betaYM t i x)) == (0, 2, 0))
    with
    | some x => fuCode x
    | none => 2047
  else 0

@[expose] def fuWit : Array (Array Nat) :=
  (Array.range 36).map fun i => (Array.range 64).map fun t => fuCell t i

@[expose] def fuPGens : Array (Array Nat) :=
  #[wordTab (wT₀.getD 0 []), wordTab (wT₀.getD 1 []), wordTab (wT₀.getD 2 []),
    wordTab (wT₀.getD 3 []), g₅T, g₆T]

@[expose] def fuId : Array Nat := idTab 42

end CertificateChecks.KernelL34FU

end
