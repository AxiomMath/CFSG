
module

public import Certificates.Kernel.SporSch.Co2M.FratSD
public import Certificates.Kernel.SporSch.Co2M.FratTr
public import Certificates.Kernel.SporSch.Co2M.FratMD
public import Certificates.Kernel.SporSch.Co2M.ChainSD
public import Certificates.Data.Kernel.SporSch.Co2Prof
public import Certificates.Data.Kernel.Co2InvS
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KC.Co2InvS CFSG.KS.Co2P
open CFSG.Sporadic.Co2Schreier

@[expose] noncomputable def swapF01 (P : ℕ) : ℕ :=
  (fun x => Nat.xor P (Nat.lor x (Nat.shiftLeft x 12)))
    (Nat.xor (pg 12 (mask 12) P 0) (pg 12 (mask 12) P 1))

theorem neg_tb : notK (bindK (PV 0) (Co2LF.TR 1) (FT0.getD 2 0) (FT0I.getD 2 0)) = true := by
  quickRfl

theorem neg_sb : notK (bindK (PV 0) (Co2LF.S 0) (fratT.getD 1 (0, 0)).1
    (fratT.getD 1 (0, 0)).2) = true := by
  quickRfl

theorem neg_siftF :notK (siftF (swapF01 (pc (pc (Co2LS.S 0) (Co2LF.S 0)) (Co2LS.SI 0)))) = true := by
  quickRfl

theorem neg_pair : siftF (pc (FY 33) (FY 1)) = true := by
  quickRfl

theorem neg_prof : notK (rowK (hA (FYZ.getD 3 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1
    (FT0.take 1) 0) (profTable.getD 3 [])) = true := by
  quickRfl

theorem neg_zs : notK (Nat.beq (cmpP zP (sT.getD 0 (0, 0))).1 (cmpP (sT.getD 0 (0, 0)) tP).1) =
    true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
