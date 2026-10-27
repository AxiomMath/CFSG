module

public import Certificates.Data.GrSLitL34Sec5SWIsoCheck

public section

namespace CertificateChecks.KernelL34W

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

@[expose] def yArr : Array (Array Nat) := (Array.range 2304).map fun n => yTab (n % 64) (n / 64)

@[expose] def outCodes : Array Nat :=
  (Array.range 2304).filter fun n =>
    !repInS.contains (n / 64) && comp 42 yArr[n]! yArr[n]! == idTab 42

@[expose] def otArr : Array (Array Nat) := outCodes.map fun n => #[n]

@[expose] def rkArr : Array (Array Nat) :=
  (Array.range 2304).map fun n => #[(outCodes.findIdx? (· == n)).getD 144]

@[expose] def cmArr : Array (Array Nat) :=
  outCodes.map fun n => outCodes.map fun n' =>
    if comp 42 yArr[n]! yArr[n']! == comp 42 yArr[n']! yArr[n]! then 1 else 0

@[expose] def encM (x : MElt) : Nat := 16 * x.1 + 4 * x.2.1.val + x.2.2.val

@[expose] def btArr : Array (Array Nat) :=
  outCodes.map fun n => (Array.range 64).map fun k => encM (betaYM (n % 64) (n / 64) (k, 0, 0))

end CertificateChecks.KernelL34W

end
