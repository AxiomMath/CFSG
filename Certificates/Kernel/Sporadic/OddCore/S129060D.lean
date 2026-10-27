module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.SuzCheck
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CertificateChecks.KernelSpor.S129060

open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

meta def tabM : Array (Array Nat) := (List.range 6).toArray.map fun k => suzATab k

meta def invM : Array (Array Nat) := tabM.map (invCand 1782)

meta def allM : Array (Array Nat) := tabM ++ invM

meta def digitsM (k : Nat) : Array Nat := #[k % 3, k / 3 % 3, k / 9 % 3, k / 27 % 3, k / 81 % 3]

meta def powM (t : Array Nat) : Nat → Array Nat
  | 0 => idA 1782
  | d + 1 => compA 1782 t (powM t d)

meta def phiM (k : Nat) : Array Nat :=
  let e := digitsM k
  (List.range 5).foldr (fun i acc => compA 1782 (powM tabM[i]! e[i]!) acc) (idA 1782)

meta def phisM : Array (Array Nat) := (List.range 243).toArray.map phiM

meta def conjM (j : Nat) : Array Nat := compA 1782 tabM[5]! (compA 1782 tabM[j]! invM[5]!)

meta def expM : Array (Array Nat) := (List.range 5).toArray.map fun j =>
  digitsM (((List.range 243).find? fun k => phisM[k]! == conjM j).getD 0)

meta def witM : Array (Array Nat) := #[(List.range 243).toArray.map fun k =>
  ((List.range 1782).find? fun p => phisM[k]![p]! != p).getD 0]

end CertificateChecks.KernelSpor.S129060

#kmisc_packarrs CertificateChecks.KernelSpor.S1290A CertificateChecks.KernelSpor.S129060.allM 11

#kmisc_packarrs CertificateChecks.KernelSpor.S1290E CertificateChecks.KernelSpor.S129060.expM 2

#kmisc_packarrs CertificateChecks.KernelSpor.S1290W CertificateChecks.KernelSpor.S129060.witM 11

end
