module

public import Certificates.Kernel.MonsterB.Quad3078Data
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMonB.Quad3078

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbW CFSG.KC.Q3078 CFSG.KD.Q3078

theorem inc : ∀ i < 14280, incB 1020 14280 65536 SB i = true := by lc_cover 7140

theorem tree : ∀ i < 14280, treeB (pairK RW CK) 45 1020 14280 0 SB TB i = true := by lc_cover 1020

theorem zd : ∀ i < 14280, zdK ZM (ptB 1020 SB i) = true := by lc_cover 7140

theorem root : Nat.beq (ptB 1020 SB 0) 1 = true := by quickRfl

theorem cnt : Nat.beq (cntK ZM 256) 120 = true := by quickRfl

theorem keep : ∀ t < 11520, keepK RW CK ZM t = true := by lc_cover 5760

theorem neg_tree : notB (treeB (pairK RW CK) 45 1020 14280 0 SB
    (Nat.xor T0 (Nat.shiftLeft 1 (Nat.add 32 16)) :: TB.tail) 1) = true := by
  quickRfl

theorem neg_zd : notB (zdK (Nat.xor ZM 1) (ptB 1020 SB 0)) = true := by quickRfl

theorem neg_keep : notB (allLt 256 fun n => keepK (Nat.xor RW 1) CK ZM n) = true := by quickRfl

theorem neg_inc : notB (incB 1020 14280 65533 SB 14279) = true := by quickRfl

end CertificateChecks.KernelMonB.Quad3078

end
