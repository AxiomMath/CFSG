
module

public import Certificates.Kernel.SporSch.Co2M.ThirdOrb
public import Certificates.Kernel.SporSch.Co2M.Class
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier

@[expose] noncomputable def t3T : List (ℕ × ℕ) := extP mmK I22 aT witRec.third.strongDerivations

meta def uArrs : Array (Array Nat) := #[uArr]

end CertificateChecks.KernelSporSch.Co2M

#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.UP CertificateChecks.KernelSporSch.Co2M.uArrs 12

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep

theorem bind_t3a : allN 10 (fun k => bindK (PV 0) (Co2T3.S k) (t3T.getD k (0, 0)).1
    (t3T.getD k (0, 0)).2) = true := by quickRfl

theorem bind_t3b : allN 10 (fun k => bindK (PV 0) (Co2T3.S (Nat.add 10 k))
    (t3T.getD (Nat.add 10 k) (0, 0)).1 (t3T.getD (Nat.add 10 k) (0, 0)).2) = true := by quickRfl

theorem bind_t3c : allN 10 (fun k => bindK (PV 0) (Co2T3.S (Nat.add 20 k))
    (t3T.getD (Nat.add 20 k) (0, 0)).1 (t3T.getD (Nat.add 20 k) (0, 0)).2) = true := by quickRfl

theorem bind_u : bindK (PV 0) (UP 0) uP.1 uP.2 = true := by quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
