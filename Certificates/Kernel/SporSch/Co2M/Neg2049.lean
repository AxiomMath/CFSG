
module

public import Certificates.Kernel.SporSch.Co2M.WordsBase
public import Certificates.Data.Kernel.Co2InvS
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KC.Co2InvS

@[expose] noncomputable def swap01 (P : ℕ) : ℕ :=
  (fun x => Nat.xor P (Nat.lor x (Nat.shiftLeft x 12)))
    (Nat.xor (pg 12 (mask 12) P 0) (pg 12 (mask 12) P 1))

theorem neg_bind_q : notK (bindK (PV 0) (WQ 0) (qT.getD 1 (0, 0)).1 (qT.getD 1 (0, 0)).2) =
    true := by quickRfl

theorem neg_orig_c : notK (bindK (PV 0) (Co2LC.S 0) (cT.getD 1 (0, 0)).1
    (cT.getD 1 (0, 0)).2) = true := by quickRfl

theorem neg_sift : notK (siftS (swap01 (WQ 0))) = true := by quickRfl

theorem neg_zt : notK (Nat.beq (cmpP zP tP).1 I22) = true := by quickRfl

theorem neg_comm : notK (Nat.beq (cmpP (cT.getD 0 (0, 0)) tP).1 (cmpP tP (cT.getD 0 (0, 0))).1) =
    true := by quickRfl

theorem neg_head : notK (headK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2LS.S Co2LS.SI 23 16
    lsD 3 Co2LS.BP) = true := by quickRfl

theorem neg_orb : notK (lvOrbSlK 2300 12 (mask 12) (2300 * 12) Co2LC.S Co2LC.SI 14
    (stepsAt 2300 12 Co2LC.S 14 Co2LC.BP 1) (Co2LC.LR 0) 0 256) = true := by quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
