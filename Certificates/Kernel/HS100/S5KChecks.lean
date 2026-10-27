module

public import Certificates.Kernel.HS100.S5KData
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.MonsterB.Co2Count
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100.S5K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.Co2Mem
open CertificateChecks.KernelHS100

theorem perm : allN 5 (fun k => permB 100 7 (F k)) = true := by quickRfl

theorem nums : (Nat.beq CS.ng 4 && Nat.beq CS.N 1024 && allN 4 (fun k => Nat.beq (CS.G k) (F k)))
    = true := by quickRfl

theorem keys : keysSK 100 7 [0, 1, 2, 3, 4] CS.N CS.T CS.SK = true := by quickRfl

theorem gensP : allN 4 (fun k => (rngK (F k) && inHS (F k)) ||
    (rngK (pm (HP.F 15) (F k)) && inHS (pm (HP.F 15) (F k)))) = true := by quickRfl

theorem z : (rngK Z && inHS Z && !Nat.beq Z (pidn 100 7) && Nat.beq (pm Z Z) (pidn 100 7) &&
    memK 1024 CS.T Z) = true := by quickRfl

theorem os : allN 1024 osOne = true := by quickRfl

theorem cnts : (Nat.beq (cntK 1024 out1) 104 && Nat.beq (cntK 1024 outZ) 40) = true := by quickRfl

end CertificateChecks.KernelHS100.S5K

end
