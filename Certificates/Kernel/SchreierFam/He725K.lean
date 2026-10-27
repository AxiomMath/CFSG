module

public import Certificates.Kernel.SchreierFam.He725S
public import Certificates.Kernel.SchreierFam.He725X
public import Certificates.Kernel.SchreierFam.He725D
public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Data.Kernel.Misc.BaseWords
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.He725

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.BaseWords
  CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def S (j : Nat) : Nat := He725S.S j

@[expose] noncomputable def SI (j : Nat) : Nat := He725S.SI j

@[expose] def bsL : List Nat := [0, 1, 2, 3, 4]

@[expose] noncomputable def QL : List Nat := [QQ 0, QQ 1, QQ 2, QQ 3]

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

theorem kG1 : Nat.beq (S 1) (pc (pc (CC 0) (S 0)) (CC 1)) = true := by quickRfl

theorem kC : permOK 8330 14 (mask 14) (8330 * 14) (CC 0) (CC 1) = true := by quickRfl

theorem kQlen : Nat.beq qL.length 4 = true := by quickRfl

theorem kSX : allN 4 (fun j => Nat.beq (He725X.S j) (S j)) = true := by quickRfl

theorem kP : allN 4 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (S j) (SI j)) = true := by
  quickRfl

theorem kBase : bAnd(allN 2 (fun t => Nat.beq (#[0, 1] : Array Nat)[t]! (pg 14 (mask 14) He725S.BP t)),
    allN 5 (fun t => Nat.beq (#[0, 1, 2, 3, 4] : Array Nat)[t]! (pg 14 (mask 14) He725X.BP t))) =
    true := by quickRfl

theorem kLast : allN 3 (fun i => Nat.beq (rcnt (He725X.LR (Nat.add 2 i))) 1) = true := by quickRfl

theorem kProd : ((List.range 2).map fun i => rcnt (He725S.LR i)).prod = 21504 := by
  decide +kernel

theorem kCn : bAnd(allN 4 (fun j => bAnd(cn (S j), cn (SI j))),
    bAnd(cn (CC 0), bAnd(cn (CC 1), allN 4 (fun i => cn (QQ i))))) = true := by quickRfl

theorem kFix : bAnd(fixBK 8330 14 bsL [S 0] 7, bIf(fixBK 8330 14 bsL [S 0] 1, false, true)) =
    true := by quickRfl

theorem kNorm : bAnd(normsWK 8330 14 bsL QL (S 0) (SI 0), normsWK 8330 14 bsL QL (CC 0) (CC 1)) =
    true := by quickRfl

theorem kNeg : fixBK 8330 14 bsL [S 0] 3 = false := by decide +kernel

end CertificateChecks.KernelSchreierFam.He725

end
