module

public import Certificates.Kernel.Misc.KGroups.U33Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GH74.KGroups.U33Inputs
public import Certificates.Data.Kernel.Misc.KGrp

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.U33K

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.KG CFSG.KC.LQT.P
open CFSG.GH74.KGroups.U33

theorem treeA0 : allR 0 3024 (treeAt (mul 28) (one 28) AG 3 EA PAA) = true := by quickRfl
theorem treeA1 : allR 3024 3024 (treeAt (mul 28) (one 28) AG 3 EA PAA) = true := by quickRfl
theorem treeA2 : allR 6048 3024 (treeAt (mul 28) (one 28) AG 3 EA PAA) = true := by quickRfl
theorem treeA3 : allR 9072 3024 (treeAt (mul 28) (one 28) AG 3 EA PAA) = true := by quickRfl
theorem sortAB : allN 12096 (sortAt 12096 EA SGA) = true := by quickRfl
theorem closedA0 : allR 0 3024 (closedAt (mul 28) AG 3 12096 EA CTA) = true := by quickRfl
theorem closedA1 : allR 3024 3024 (closedAt (mul 28) AG 3 12096 EA CTA) = true := by quickRfl
theorem closedA2 : allR 6048 3024 (closedAt (mul 28) AG 3 12096 EA CTA) = true := by quickRfl
theorem closedA3 : allR 9072 3024 (closedAt (mul 28) AG 3 12096 EA CTA) = true := by quickRfl

theorem repB : andB (andB (inA (RG 0)) (ordK 28 (RG 0) 2)) (andB (andB (inA (RG 1))
    (ordK 28 (RG 1) 3)) (andB (inA (RG 2)) (ordK 28 (RG 2) 3))) = true := by quickRfl
theorem c2AB : Nat.beq (cntN 12096 fun k => ordK 28 (EA k) 2) 315 = true := by quickRfl
theorem cAuB : Nat.beq (cntN 12096 fun k => comm 28 (EA k) (UG 0)) 192 = true := by quickRfl
theorem cAtB : Nat.beq (cntN 12096 fun k => comm 28 (EA k) (RG 0)) 48 = true := by quickRfl
theorem centAB : allN 12096 (centAt 28 EA (UG 0) (UG 1)) = true := by quickRfl
theorem inuB : allN 12096 (inC3At 28 EA (UG 0) CLu) = true := by quickRfl
theorem intB : allN 12096 (inC3At 28 EA (RG 0) CLt) = true := by quickRfl
theorem e9uB : e9K 28 CLu = true := by quickRfl
theorem e9tB : e9K 28 CLt = true := by quickRfl
theorem c3AB : Nat.beq (cntN 12096 fun k => ordK 28 (EA k) 3) 728 = true := by quickRfl
theorem cA1B : Nat.beq (cntN 12096 fun k => comm 28 (EA k) (RG 1)) 216 = true := by quickRfl
theorem cA2B : Nat.beq (cntN 12096 fun k => comm 28 (EA k) (RG 2)) 18 = true := by quickRfl
theorem in1B : allN 12096 (inC3At 28 EA (RG 1) CL1) = true := by quickRfl
theorem in2B : allN 12096 (inC3At 28 EA (RG 2) CL2) = true := by quickRfl
theorem e27aB : e27K 28 (RG 1) CL1 = true := by quickRfl
theorem e27bB : e27K 28 (RG 2) CL2 = true := by quickRfl

theorem ordUVB : andB (ordK 28 (UG 0) 2) (andB (ordK 28 (UG 1) 7) (pairK 28 (UG 0) (UG 1) wsU)) =
    true := by quickRfl

end CertificateChecks.KernelMisc.U33K

end
