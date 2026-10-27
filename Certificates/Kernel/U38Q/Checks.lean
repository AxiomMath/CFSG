module

public import Certificates.Kernel.U38Q.Data
public import Certificates.Kernel.U38.Data
public import Certificates.Kernel.SchreierFam.C188001C1
public import Certificates.Data.Kernel.U38QK
public import Certificates.Data.Kernel.K426K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38Q

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.K426K CFSG.KC.U38QK
  CFSG.KS.PEnum
open CertificateChecks.KernelSchreierFam CertificateChecks.KernelU38

local notation "S1" G => siftOK 513 10 3 U38C1.LR U38C1.TRI U38C1.BP G
local notation "SX" G => siftOK 513 10 4 UX.LR UX.TRI UX.BP G
local notation "PM" => pcomp 513 10 (mask 10)

theorem q211SzOK : szOK 513 10 = true := by quickRfl

theorem q211Perm : allN 3 (fun j => permB 513 10 (QH.F j)) = true := by quickRfl

theorem q211Nums : Nat.beq QE.N 729 = true ∧ Nat.beq QE.ng 3 = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem q211Gens : allN 3 (fun j => Nat.beq (QE.G j) (QH.F j)) = true := by quickRfl

theorem q211Sift1 : allN 3 (fun j => S1 (QH.F j)) = true := by quickRfl

theorem q211InX : selFrom (fun i => SX (QE.T i)) 729 0 XI = true := by quickRfl

theorem q211Lens : Nat.beq XI.length 81 = true ∧ Nat.beq CA.length 63 = true ∧
    Nat.beq CB.length 54 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem q211WA : pairK (fun i j => Nat.beq (PM (QH.F 0) (QE.T i)) (QE.T j)) XI WA = true := by
  quickRfl

theorem q211WB : pairK (fun i j => Nat.beq (PM (QH.F 1) (QE.T i)) (QE.T j)) XI WB = true := by
  quickRfl

theorem q211CA : selL (fun j => cubeK 513 10 (QE.T j)) WA CA = true := by quickRfl

theorem q211CB : selL (fun j => cubeK 513 10 (QE.T j)) WB CB = true := by quickRfl

theorem q211NoComm : noCommK 513 10 [0, 167, 270] QE.T CA CB = true := by quickRfl

end CertificateChecks.KernelU38Q

end
