module

public import Certificates.Kernel.G24Tri.Text27206
public import Certificates.Kernel.G24Tri.Pack27206
public import Certificates.Kernel.G24Tri.Chain27206
public import Certificates.Kernel.Co1B.Orb2045
public import Certificates.Data.Kernel.G24Tri
public import Certificates.Data.Kernel.Co1BPair
public import Certificates.Data.Kernel.LBind
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24.Tri27206

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Co1BPair CFSG.KC.G24Tri

@[expose] noncomputable def sP (i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (PK 6) (fun j _ => Nat.rec (motive := fun _ => Nat) (LC.S 0)
    (fun _ _ => PK 7) j) i

@[expose] def mT (i : Nat) : Nat := [5, 5, 7].getD i 0

theorem kGoodT : (TT.chars.splitOn ' ').all goodP = true := by quickRfl
theorem kGoodL : (LT.chars.splitOn ' ').all goodP = true := by quickRfl
theorem kM : ((List.range 3).all fun i =>
    Nat.beq ((numsOf TT.chars).toArray[i * 2731]!) (mT i)) = true := by quickRfl
theorem kBindT : ((List.range 3).all fun i =>
    lbindK ((numsOf TT.chars).extract (i * 2731 + 1) (i * 2731 + 1366)) 1365 11 (PK (2 * i)) &&
      lbindK ((numsOf TT.chars).extract (i * 2731 + 1366) (i * 2731 + 2731)) 1365 11
        (PK (2 * i + 1))) = true := by quickRfl
theorem kBindL : (lbindK ((numsOf LT.chars).extract 0 1365) 1365 11 (PK 6) &&
    lbindK ((numsOf LT.chars).extract 17743 19108) 1365 11 (PK 7)) = true := by quickRfl
theorem kCan : allN 8 (fun k => canonK 1365 11 (mask 11) (1365 * 11) (PK k)) = true := by quickRfl
theorem kInv : allN 6 (fun k => invEqK 1365 11 (mask 11) (1365 * 11) (PK k) (PK (8 + k))) = true :=
  by quickRfl
theorem kSift : allN 6 (fun k =>
    siftK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) LC.LR LC.TRI LC.BP 3 0 (PK k)) = true := by
  quickRfl
theorem kSR : allN 6 (fun j => Nat.beq (CertificateChecks.KernelCo1B.Tri2045.RO.S j) (LC.S j)) =
    true := by quickRfl
theorem kP : allN 6 (fun j => permOK 1365 11 (mask 11) (1365 * 11) (LC.S j) (LC.SI j)) = true := by
  quickRfl
theorem kB : allN 3 (fun t => Nat.beq (pg 11 (mask 11) LC.BP t) t) = true := by quickRfl
theorem kComm : allN 3 (fun i =>
    canonK 1365 11 (mask 11) (1365 * 11) (sP i) &&
    Nat.beq (pcomp 1365 11 (mask 11) (PK (2 * i)) (sP i))
      (pcomp 1365 11 (mask 11) (sP i) (PK (2 * i))) &&
    Nat.beq (pcomp 1365 11 (mask 11) (PK (2 * i + 1)) (sP i))
      (pcomp 1365 11 (mask 11) (sP i) (PK (2 * i + 1)))) = true := by quickRfl
theorem kOrd : allN 3 (fun i =>
    ordAuxK (PK (2 * i)) 1 (PK (2 * i)) && ordAuxK (PK (2 * i + 1)) 2 (PK (2 * i + 1)) &&
    ordAuxK (pcomp 1365 11 (mask 11) (PK (2 * i)) (PK (2 * i + 1))) (mT i - 1)
      (pcomp 1365 11 (mask 11) (PK (2 * i)) (PK (2 * i + 1)))) = true := by quickRfl

end CertificateChecks.KernelG24.Tri27206

end
