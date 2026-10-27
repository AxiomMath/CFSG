module

public import Certificates.Kernel.U38Fix.Data
public import Certificates.Kernel.U38.Data
public import Certificates.Kernel.SchreierFam.C188001H
public import Certificates.Kernel.SchreierFam.C188001C1
public import Certificates.Data.Kernel.U38FixK
public import Certificates.Data.Kernel.K426K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38Fix

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.K426K CFSG.KC.U38QK CFSG.KC.U38FixK
  CFSG.KC.Misc.ArrEnum CFSG.KS.PEnum
open CertificateChecks.KernelSchreierFam CertificateChecks.KernelU38 CertificateChecks.KernelU38Q

local notation "S1" G => siftOK 513 10 3 U38C1.LR U38C1.TRI U38C1.BP G
local notation "SX" G => siftOK 513 10 4 UX.LR UX.TRI UX.BP G
local notation "PM" => pcomp 513 10 (mask 10)

@[expose] noncomputable def hT (t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (FH.F (Nat.add 4 t)) (pidn 513 10) (Nat.beq t 0)

@[expose] noncomputable def eK (e : Nat) : Nat := E0K.getD e 0

theorem fx419Perm : allN 8 (fun j => permB 513 10 (FH.F j)) = true := by quickRfl

theorem fx419Nums : Nat.beq HE.N 378 = true ∧ Nat.beq HE.ng 2 = true := ⟨by quickRfl, by quickRfl⟩

theorem fx419Gens : allN 2 (fun j => Nat.beq (HE.G j) (FH.F j)) = true := by quickRfl

theorem fx419Sift1 : allN 2 (fun j => S1 (FH.F j)) = true := by quickRfl

theorem fx419Fix : allN 2 (fun j => Nat.beq (pg 10 (mask 10) (FH.F j) 109) 109 &&
      Nat.beq (pg 10 (mask 10) (FH.F j) 458) 458) = true ∧
    Nat.beq (pg 10 (mask 10) (U38A.F 31) 109) 109 = true ∧
    Nat.beq (pg 10 (mask 10) (U38A.F 31) 458) 458 = true ∧ (SX (U38A.F 31)) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem fx419FixOK : allN 378 (fun i => fixRowK 513 10 (U38A.F 31) (fun G => SX G) (HE.T i)) = true := by
  quickRfl

theorem fx419FixWit : (Nat.blt (FW.getD 0 0) 378 && cubeK 513 10 (HE.T (FW.getD 0 0)) &&
    commK 513 10 (HE.T (FW.getD 0 0)) (U38A.F 31) && !Nat.beq (HE.T (FW.getD 0 0)) (pidn 513 10) &&
    (SX (HE.T (FW.getD 0 0)))) = true := by
  quickRfl

theorem fx419X : allN 6 (fun j => SX (FH.F (Nat.add 2 j))) = true := by quickRfl

theorem fx419E : (cubeK 513 10 (FH.F 3) && cubeK 513 10 (FH.F 4) &&
    !Nat.beq (FH.F 3) (pidn 513 10) && !Nat.beq (FH.F 4) (pidn 513 10) &&
    !Nat.beq (FH.F 4) (FH.F 3) && !Nat.beq (FH.F 4) (PM (FH.F 3) (FH.F 3)) &&
    commK 513 10 (FH.F 3) (FH.F 4) && commK 513 10 (FH.F 2) (FH.F 3) &&
    Nat.beq (PM (FH.F 2) (FH.F 4)) (PM (PM (FH.F 4) (FH.F 4)) (FH.F 2))) = true := by
  quickRfl

theorem fx419E0 : allN 3 (fun a => allN 3 (fun b => Nat.beq (eK (Nat.add (Nat.mul 3 a) b))
    (PM (pw3K 513 10 (FH.F 3) a) (pw3K 513 10 (FH.F 4) b)))) = true := by
  quickRfl

theorem fx419Cover : pairK (coverRowK 513 10 QE.T hT eK XI) XI CV = true := by quickRfl

end CertificateChecks.KernelU38Fix

end
