module

public import CFSG.Certificates.Kernel.Spor.OrdSound
public import Certificates.Data.Kernel.Spor.SuzBridge
public import Certificates.Kernel.Sporadic.SuzBridge.Regs
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Th.S.Chars

public section

set_option maxRecDepth 400000

#th_chars CFSG.KD.SuzB.LA CFSG.Blueprint.NativeSporadic.SuzSeed1
#th_chars CFSG.KD.SuzB.LB CFSG.Blueprint.NativeSporadic.SuzSeed2

namespace CertificateChecks.KernelSpor.SuzBridge

open CFSG CFSG.KC.Ord CFSG.KS.Ord CFSG.KD.SuzB

theorem consts : constsOK 3 10 640 64 7 L H CM RM ONE LV HV = true := by quickRfl

theorem bytes1 : CFSG.KS.Bytes.bytesEqK LA P1 256 4181 = true := by quickRfl

theorem bytes2 : CFSG.KS.Bytes.bytesEqK LB P2 256 4181 = true := by quickRfl

theorem dec1 : Nat.beq (decRun P1 256 4181 3 64 10 640 RM (RB 1) (List.range 17) 1) St1 = true :=
  by quickRfl

theorem dec2 : Nat.beq (decRun P2 256 4181 3 64 10 640 RM (RB 2) (List.range 17) 1) St2 = true :=
  by quickRfl

theorem done1 : seedDone 64 (validM 3 40960 L H) (RB 1) St1 = true := by quickRfl

theorem done2 : seedDone 64 (validM 3 40960 L H) (RB 2) St2 = true := by quickRfl

theorem roots : rootsOK RB (validM 3 40960 L H) 1 (9 + 1) = true := by quickRfl

theorem invs : invsOK RB (mulR 3 10 640 64 7 L H CM RM) (validM 3 40960 L H) 9 ONE = true := by
  quickRfl

theorem relN : Nat.beq (lenRels rels) 43 = true := by quickRfl

theorem relB : relsBounded rels 9 = true := by quickRfl

theorem relsAll :
    (List.range 43).all (fun r => relOK RB (mulR 3 10 640 64 7 L H CM RM) rels 9 ONE r) = true := by
  quickRfl

theorem seedA : Blueprint.NativeSporadic.decode 3 64 1 Blueprint.NativeSporadic.SuzSeed1 =
    ordMat 3 64 10 640 (RB 1) := by
  rw [LA_eq]
  exact seed_sound (hnb := rfl) consts bytes1 rfl dec1 done1

theorem seedB : Blueprint.NativeSporadic.decode 3 64 1 Blueprint.NativeSporadic.SuzSeed2 =
    ordMat 3 64 10 640 (RB 2) := by
  rw [LB_eq]
  exact seed_sound (hnb := rfl) consts bytes2 rfl dec2 done2

end CertificateChecks.KernelSpor.SuzBridge

end
