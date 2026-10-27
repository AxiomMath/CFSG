module

public import Certificates.Kernel.U38Three.Data
public import Certificates.Kernel.U38Three.PData
public import Certificates.Kernel.U38.Data
public import Certificates.Kernel.SchreierFam.C188001C1
public import Certificates.Data.Kernel.U38ThreeK
public import Certificates.Data.Kernel.K426K
public import Certificates.Data.Kernel.Misc.ChainTail
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.K426K CFSG.KC.U38QK CFSG.KC.U38ThreeK
  CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CertificateChecks.KernelSchreierFam CertificateChecks.KernelU38

local notation "S1" G => siftOK 513 10 3 U38C1.LR U38C1.TRI U38C1.BP G
local notation "SX" G => siftOK 513 10 4 UX.LR UX.TRI UX.BP G
local notation "PM" => pcomp 513 10 (mask 10)
local notation "I5" => pidn 513 10

@[expose] def rels810201 : List (Nat × Nat × Nat) := [(0, 0, 1), (1, 1, 1), (2, 2, 1)]

theorem ch810201Perm : allN 7 (fun j => permB 513 10 (FT.F j)) = true := by quickRfl

theorem ch810201Nums : (Nat.beq HE.N 378 && Nat.beq HE.ng 2 && Nat.beq LE.N 504 &&
    Nat.beq LE.ng 2 && Nat.beq CE.N 1512 && Nat.beq CE.ng 2) = true := by
  quickRfl

theorem ch810201Gens : allN 2 (fun j => Nat.beq (HE.G j) (FT.F (Nat.add 1 j)) &&
    Nat.beq (LE.G j) (FT.F (Nat.add 3 j)) && Nat.beq (CE.G j) (FT.F (Nat.add 5 j))) = true := by
  quickRfl

theorem ch810201Sift1 : allN 3 (fun j => (S1 (FT.F j)) &&
    Nat.beq (pg 10 (mask 10) (FT.F j) 0) 0 && Nat.beq (pg 10 (mask 10) (FT.F j) 1) 1) = true := by
  quickRfl

theorem ch810201D0 : (cubeK 513 10 (FT.F 0) && !Nat.beq (FT.F 0) I5) = true := by quickRfl

theorem ch810201Elem : hElemK 513 10 378 HE.T (FT.F 0) (PM (FT.F 0) (FT.F 0)) = true := by
  quickRfl

theorem ch810201SiftX : allN 4 (fun j => SX (FT.F (Nat.add 3 j))) = true := by quickRfl

theorem ch810201Comm : (CFSG.KC.U38FixK.commK 513 10 (FT.F 3) (FT.F 0) &&
    CFSG.KC.U38FixK.commK 513 10 (FT.F 4) (FT.F 0)) = true := by
  quickRfl

theorem ch810201Rels : (CFSG.KC.B3S3K.relsK 513 10 3 UX.BP (FT.F 0) 4 rels810201 &&
    CFSG.KC.B3S3K.commK 513 10 2 (FT.F 0) CE.G && Nat.beq (rcnt (UX.LR 0)) 513) = true := by
  quickRfl

theorem ch810201Tail : allN 513 (ptailBranchK 513 10 UX.LR UX.TR UX.BP (FT.F 0)
    (CFSG.KC.B3S3K.pw 513 10 (FT.F 0)) rels810201 CE.N CE.T 4) = true := by
  quickRfl

theorem ch810201Mem : allN 2 (fun k => allN 2 (fun x =>
    Nat.blt (MW.getD (Nat.add (Nat.mul 4 k) (Nat.mul 2 x)) 0) 504 &&
    Nat.beq (LE.T (MW.getD (Nat.add (Nat.mul 4 k) (Nat.mul 2 x)) 0))
      (CFSG.KC.B3S3K.cj 513 10 (FT.F (Nat.add 5 k)) (FT.F (Nat.add 3 x))) &&
    Nat.blt (MW.getD (Nat.add (Nat.add (Nat.mul 4 k) (Nat.mul 2 x)) 1) 0) 504 &&
    Nat.beq (LE.T (MW.getD (Nat.add (Nat.add (Nat.mul 4 k) (Nat.mul 2 x)) 1) 0))
      (cjInv 513 10 (FT.F (Nat.add 5 k)) (FT.F (Nat.add 3 x))))) = true := by
  quickRfl

theorem ch810201LP : allN 9 (fun j => Nat.beq (pg 10 (mask 10) (FT.F 3) j) (pg 4 (mask 4) (PE.G 0) j) &&
    Nat.beq (pg 10 (mask 10) (FT.F 4) j) (pg 4 (mask 4) (PE.G 1) j)) = true := by
  quickRfl

end CertificateChecks.KernelU38Three

end
