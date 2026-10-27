module

public import Certificates.Kernel.Misc.KGroups.U33Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GH74.KGroups.U33Inputs
public import Certificates.Data.Kernel.Misc.KGrp

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.U33K

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.KG CFSG.KC.LQT
open CFSG.KC.LQT.P CFSG.GH74.KGroups.U33

theorem treeP0 : allR 0 1512 (treeAt (mul 28) (one 28) AG 2 EP PAP) = true := by quickRfl
theorem treeP1 : allR 1512 1512 (treeAt (mul 28) (one 28) AG 2 EP PAP) = true := by quickRfl
theorem treeP2 : allR 3024 1512 (treeAt (mul 28) (one 28) AG 2 EP PAP) = true := by quickRfl
theorem treeP3 : allR 4536 1512 (treeAt (mul 28) (one 28) AG 2 EP PAP) = true := by quickRfl
theorem sortPB : allN 6048 (sortAt 6048 EP SGP) = true := by quickRfl
theorem closedP0 : allR 0 1512 (closedAt (mul 28) AG 2 6048 EP CTP) = true := by quickRfl
theorem closedP1 : allR 1512 1512 (closedAt (mul 28) AG 2 6048 EP CTP) = true := by quickRfl
theorem closedP2 : allR 3024 1512 (closedAt (mul 28) AG 2 6048 EP CTP) = true := by quickRfl
theorem closedP3 : allR 4536 1512 (closedAt (mul 28) AG 2 6048 EP CTP) = true := by quickRfl

theorem memB : andB (inP (UG 0)) (andB (inP (UG 1)) (andB (inP (P.conj 28 (AG 2) (UG 0)))
    (inP (P.conj 28 (AG 2) (UG 1))))) = true := by quickRfl
theorem wordB : allN 2 (fun j => andB (lettersK 2 (WAB j))
    (Nat.beq (wordK 28 UG 2 (WAB j)) (AG j))) = true := by quickRfl
theorem c2PB : Nat.beq (cntN 6048 fun k => ordK 28 (EP k) 2) 63 = true := by quickRfl
theorem fibPB : Nat.beq (cntN 6048 (fibAt 28 EP (UG 0) 7 wsU)) 192 = true := by quickRfl
theorem cPuB : Nat.beq (cntN 6048 fun k => comm 28 (EP k) (UG 0)) 96 = true := by quickRfl
theorem cPtB : Nat.beq (cntN 6048 fun k => comm 28 (EP k) (RG 0)) 24 = true := by quickRfl

end CertificateChecks.KernelMisc.U33K

end
