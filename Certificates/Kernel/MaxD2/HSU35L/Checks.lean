module

public import Certificates.Kernel.MaxD2.HSU.Data
public import Certificates.Data.ThreeFourTwoHSU35
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSU35L

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelMaxD2.HSU Certificates.ThreeFourTwoHSU35

@[expose] noncomputable def TK (k : Nat) : Nat :=
  wordK 100 7 (mask 7) (pidn 100 7) GP GPI (hsU35GenWords.getD k [])

theorem wq : allN 6 (fun k => wordEqK 100 7 (mask 7) (pidn 100 7) GP GPI 2
    (hsU35GenWords.getD k []) (TK k)) = true := by
  quickRfl

theorem actK : allN 6 (fun k => allN 50 (fun i => Nat.beq (pg 7 (mask 7) (TK k) hsU35Labels[i]!)
    hsU35Labels[(HNUnitaryBridge.smallPerms[k]!)[i]!]!)) = true := by
  quickRfl

end CertificateChecks.KernelMaxD2.HSU35L

end
