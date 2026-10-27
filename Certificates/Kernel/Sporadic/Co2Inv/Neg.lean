module

public import Certificates.Kernel.Sporadic.Co2Inv.Gens
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSpor.Co2Inv

open CFSG.KC.Co2InvS CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.M1F2

@[expose] noncomputable def Gbad (j : Nat) : Nat := Nat.xor (G j) (nIf(Nat.beq j 2, 1, 0))

@[expose] noncomputable def CFbad (c : Nat) : Nat := E.CF (Nat.xor c (nIf(Nat.blt c 2, 1, 0)))

@[expose] noncomputable def swap01 (P : Nat) : Nat :=
  (fun x => Nat.xor P (Nat.lor x (Nat.shiftLeft x 12)))
    (Nat.xor (pg 12 (mask 12) P 0) (pg 12 (mask 12) P 1))

theorem pos_rec : recOK E.CF G YT FW 262144 12 = true := by quickRfl
theorem neg_recN : notK (recOK E.CF G YT FW 262143 262143) = true := by quickRfl
theorem neg_recG : notK (recOK E.CF Gbad YT FW 262144 0) = true := by quickRfl
theorem neg_recFW : notK (recOK E.CF G YT (fun _ => 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095) 262144 12) = true := by
  quickRfl
theorem neg_recCF : notK (recOK CFbad G YT FW 262144 64) = true := by quickRfl

theorem pos_blk : blkOK E.CF YT FW CNT 262144 0 = true := by quickRfl
theorem neg_blk : notK (blkOK E.CF YT FW (fun _ => 0) 262144 0) = true := by quickRfl
theorem pos_first : firstOK YT (elemAt E.CF 12) (fwAt FW 12) = true := by quickRfl
theorem neg_first : notK (firstOK YT (elemAt E.CF 12) (Nat.succ (fwAt FW 12))) = true := by quickRfl

theorem pos_cand : Nat.beq (mulV (WT 0) (WT 54)) IDP = true := by quickRfl
theorem neg_cand : notK (Nat.beq (mulV (WT 0) (WT 55)) IDP) = true := by quickRfl

theorem neg_vec : notK (Nat.beq (vmF 22 (WT 108) (pg 22 (mask 22) VP 1))
    (pg 22 (mask 22) VP (pg 12 (mask 12) (PT 1) 1))) = true := by quickRfl
theorem neg_inv : notK (invEqK 2300 12 (mask 12) (2300 * 12) (PT 0) (PT 6)) = true := by quickRfl
theorem neg_sift : notK (siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2A.LR Co2A.TRI
    Co2A.BP 6 0 (swap01 (PT 0))) = true := by quickRfl

end CertificateChecks.KernelSpor.Co2Inv

end
