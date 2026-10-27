module

public import Certificates.Kernel.HSPinned6101.Data

public section

namespace CertificateChecks.KernelHSPinned6101

open Certificates.Kernel.HSPinned6101

set_option maxRecDepth 100000

theorem vab_ok : allR 0 100 (vabAt VAB) = true := by decide +kernel

theorem nA_eq : dA.n = 2200 := by decide +kernel

theorem nN_eq : dN.n = 7700 := by decide +kernel

theorem headA : headOK dA 4 = true := by decide +kernel

theorem headN : headOK dN 1 = true := by decide +kernel

theorem pairsA : allR 0 2200 (pairAt dA VAB) = true := by decide +kernel

theorem pairsN0 : allR 0 2000 (pairAt dN VAB) = true := by decide +kernel

theorem pairsN1 : allR 2000 2000 (pairAt dN VAB) = true := by decide +kernel

theorem pairsN2 : allR 4000 2000 (pairAt dN VAB) = true := by decide +kernel

theorem pairsN3 : allR 6000 1700 (pairAt dN VAB) = true := by decide +kernel

theorem posA0 : allR 0 5000 (posAt dA) = true := by decide +kernel

theorem posA1 : allR 5000 5000 (posAt dA) = true := by decide +kernel

theorem posN0 : allR 0 5000 (posAt dN) = true := by decide +kernel

theorem posN1 : allR 5000 5000 (posAt dN) = true := by decide +kernel

theorem coverA : allR 0 100 (fun x => allR 0 100 (coverAt dA (adjK LM) x)) = true := by
  decide +kernel

theorem coverN : allR 0 100 (fun x => allR 0 100 (coverAt dN (nonK LM) x)) = true := by
  decide +kernel

end CertificateChecks.KernelHSPinned6101

end
