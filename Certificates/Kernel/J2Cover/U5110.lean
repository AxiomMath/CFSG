module

public import Certificates.Kernel.J2Cover.M22Lk
public import CFSG.GH74.KGroups.CoverJ2TablesInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J2ModelsGen
public import Certificates.Kernel.J2Cover.M22Blocks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.GH74.KGroups.J2

@[expose] noncomputable def mulU (p q : ℕ × ℕ) : ℕ × ℕ :=
  ((p.1 + q.1 + (if (fRK p.2).testBit q.2 then 1 else 0)) % 2, mtK p.2 q.2)

@[expose] def memU (x : ℕ × ℕ) : Bool := uList.any fun y => Nat.beq y.1 x.1 && Nat.beq y.2 x.2

@[expose] def maskU : Nat := uList.foldr (fun p acc => acc ||| (1 <<< (128 * p.1 + p.2))) 0

@[expose] def bitU (x : ℕ × ℕ) : Bool :=
  Nat.blt x.1 2 && Nat.blt x.2 128 && maskU.testBit (128 * x.1 + x.2)

@[expose] def nodupU : List (ℕ × ℕ) → Bool
  | [] => true
  | x :: xs => !(xs.elem x) && nodupU xs

theorem k5110_lt : uList.all (fun p => Nat.blt p.1 2 && Nat.blt p.2 128) = true := by quickRfl

theorem k5110_nodup : nodupU uList = true := by quickRfl

theorem k5110_mask : allN 256 (fun c => !(maskU.testBit c) || memU (c / 128, c % 128)) = true := by
  quickRfl

theorem k5110_mul : uList.all (fun p => uList.all fun q => bitU (mulU p q)) = true := by
  quickRfl

theorem k5110_inv : uList.all (fun p => uList.any fun q => mulU p q == (0, 0)) = true := by
  quickRfl

theorem k5110_central : uList.all (fun p => mulU nElt p == mulU p nElt) = true := by quickRfl

theorem k5110_sq : uList.all (fun p => mulU p p == (0, 0) || mulU p p == nElt) = true := by
  quickRfl

theorem k5110_comm : uList.all (fun p => uList.all fun q =>
    mulU p q == mulU (0, 0) (mulU q p) || mulU p q == mulU nElt (mulU q p)) = true := by
  quickRfl

theorem k5110_nsq : mulU nElt nElt == (0, 0) := by quickRfl

theorem k5110_neg_mul :
    (!((0, 2) :: uList).all (fun p => uList.all fun q => bitU (mulU p q))) = true := by
  quickRfl

theorem k5110_neg_nodup : (!nodupU ((0, 0) :: uList)) = true := by quickRfl

end CertificateChecks.KernelJ2Cover
