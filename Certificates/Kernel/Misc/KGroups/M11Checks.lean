module

public import Certificates.Kernel.Misc.KGroups.M11Data
public import Certificates.Kernel.Misc.KGroups.M11Tabs
public import Certificates.Data.Kernel.Misc.KGrp
public import Certificates.Data.Kernel.Misc.PermM22
public import CFSG.GH74.KGroups.M11Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.M11K

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.KG CFSG.KC.LQT.P
open CFSG.GH74.KGroups.M11

@[expose] noncomputable def AG (a : Nat) : Nat := nthL genL a

theorem tree0 : allR 0 1980 (treeAt (mul 11) (one 11) AG 2 E PA) = true := by quickRfl
theorem tree1 : allR 1980 1980 (treeAt (mul 11) (one 11) AG 2 E PA) = true := by quickRfl
theorem tree2 : allR 3960 1980 (treeAt (mul 11) (one 11) AG 2 E PA) = true := by quickRfl
theorem tree3 : allR 5940 1980 (treeAt (mul 11) (one 11) AG 2 E PA) = true := by quickRfl
theorem sortB : allN 7920 (sortAt 7920 E SG) = true := by quickRfl
theorem closed0 : allR 0 1980 (closedAt (mul 11) AG 2 7920 E CT) = true := by quickRfl
theorem closed1 : allR 1980 1980 (closedAt (mul 11) AG 2 7920 E CT) = true := by quickRfl
theorem closed2 : allR 3960 1980 (closedAt (mul 11) AG 2 7920 E CT) = true := by quickRfl
theorem closed3 : allR 5940 1980 (closedAt (mul 11) AG 2 7920 E CT) = true := by quickRfl

theorem ordAB : andB (ordK 11 (AG 0) 2) (andB (ordK 11 (AG 1) 4) (pairK 11 (AG 0) (AG 1) ws)) =
    true := by quickRfl
theorem x0B : andB (Nat.beq (E ix0) X0) (ordK 11 X0 3) = true := by quickRfl
theorem c2B : Nat.beq (cntN 7920 fun k => ordK 11 (E k) 2) 165 = true := by quickRfl
theorem cAB : Nat.beq (cntN 7920 fun k => comm 11 (E k) (AG 0)) 48 = true := by quickRfl
theorem cFB : Nat.beq (cntN 7920 (fibAt 11 E (AG 0) 4 ws)) 48 = true := by quickRfl
theorem centB : allN 7920 (centAt 11 E (AG 0) (AG 1)) = true := by quickRfl
theorem c3B : Nat.beq (cntN 7920 fun k => ordK 11 (E k) 3) 440 = true := by quickRfl
theorem cXB : Nat.beq (cntN 7920 fun k => comm 11 (E k) X0) 18 = true := by quickRfl
theorem inAB : allN 7920 (inC3At 11 E (AG 0) CLA) = true := by quickRfl
theorem inXB : allN 7920 (inCAt 11 E X0 CLX) = true := by quickRfl
theorem e9B : e9K 11 CLA = true := by quickRfl
theorem cent3B : cent3K 11 X0 CLX = true := by quickRfl

end CertificateChecks.KernelMisc.M11K

end
