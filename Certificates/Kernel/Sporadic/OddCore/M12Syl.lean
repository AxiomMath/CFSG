module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.GH74M12RankCheck
meta import Certificates.Data.GH74M12RankCheck
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.M12Syl

open CFSG.GH74.Generic.S45.EvSpor CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 24

meta def ids4M : Array (Array Nat) := Array.replicate 4 idM

meta def sM : Array (Array Nat) := #[natArr m12TA, natArr m12TB, natArr m12TY, natArr m12TX]

meta def siM : Array (Array Nat) := sM.map (CFSG.Monster.B.Co2.Native.invCand 24)

meta def lM : Array (Array Nat) :=
  #[natArr m12A1T, natArr m12B1T, CFSG.Monster.B.Co2.Native.invCand 24 (natArr m12A1T),
    CFSG.Monster.B.Co2.Native.invCand 24 (natArr m12B1T)]

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 24 idM sM[j]! t) 4 idM 3000).tabs

meta def clM : Array (Array Nat) := (recM.map fun x => (sM ++ siM).map fun g => comp 24 x g).flatten

end CertificateChecks.KernelSpor.M12Syl

#kmulh CertificateChecks.KernelSpor.M12S 24 5 CertificateChecks.KernelSpor.M12Syl.ids4M
  CertificateChecks.KernelSpor.M12Syl.sM CertificateChecks.KernelSpor.M12Syl.idM 3000
#kmisc_packarrs CertificateChecks.KernelSpor.M12SI CertificateChecks.KernelSpor.M12Syl.siM 5
#kmisc_packarrs CertificateChecks.KernelSpor.M12L CertificateChecks.KernelSpor.M12Syl.lM 5
#kfind CertificateChecks.KernelSpor.M12Cl CertificateChecks.KernelSpor.M12Syl.recM
  CertificateChecks.KernelSpor.M12Syl.clM

namespace CertificateChecks.KernelSpor.M12Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.GH74.Generic.S45.EvSpor CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 24 5 (mask 5) p q

@[expose] noncomputable def idK : Nat := pidn 24 5

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 24 5 (mask 5) (24 * 5) p

theorem tabs_eq : natArr m12A1T = unpack 24 5 (M12L 0) ∧ natArr m12B1T = unpack 24 5 (M12L 1) := by
  decide +kernel

theorem base_ok : bAnd(szOK 24 5, bAnd(cK idK, bAnd(CFSG.KS.Prim.idK 24 5 (mask 5),
    bAnd(allN 4 (fun j => cK (M12L j)), bAnd(allN 4 (fun j => cK (M12SI j)),
    bAnd(invEqK 24 5 (mask 5) (24 * 5) (M12L 0) (M12L 2),
    bAnd(invEqK 24 5 (mask 5) (24 * 5) (M12L 1) (M12L 3),
    bAnd(allN 4 (fun j => invEqK 24 5 (mask 5) (24 * 5) (M12S.GI j) (M12SI j)),
    bAnd(allN 4 (fun j => Nat.beq (M12S.G j) idK),
    bAnd(Nat.beq (M12S.GI 0) (wfoldK 24 5 (mask 5) M12L m12WA idK),
    bAnd(Nat.beq (M12S.GI 1) (wfoldK 24 5 (mask 5) M12L m12WB idK),
    bAnd(Nat.beq (M12S.GI 2) (wfoldK 24 5 (mask 5) M12L m12WY idK),
    bAnd(Nat.beq (M12S.GI 3) (wfoldK 24 5 (mask 5) M12L m12WX idK),
    bAnd(Nat.beq M12S.cnt 64, penumHdK idK M12S.cnt 3000 M12S.T M12S.PL)))))))))))))) = true := by
  quickRfl

theorem rels_ok :
    bAnd(Nat.beq (pc (M12S.GI 0) (pc (M12S.GI 0) (pc (M12S.GI 0) (pc (M12S.GI 0) idK)))) idK,
    bAnd(Nat.beq (pc (M12S.GI 1) (pc (M12S.GI 1) (pc (M12S.GI 1) (pc (M12S.GI 1) idK)))) idK,
    bAnd(Nat.beq (pc (M12S.GI 0) (M12S.GI 1)) (pc (M12S.GI 1) (M12S.GI 0)),
    bAnd(Nat.beq (pc (M12S.GI 2) (M12S.GI 2)) idK,
    bAnd(Nat.beq (pc (M12S.GI 3) (M12S.GI 3)) idK,
    bAnd(Nat.beq (pc (M12S.GI 2) (M12S.GI 3)) (pc (M12S.GI 3) (M12S.GI 2)),
    bAnd(Nat.beq (pc (pc (M12S.GI 2) (M12S.GI 0)) (M12SI 2)) (M12S.GI 1),
    bAnd(Nat.beq (pc (pc (M12S.GI 2) (M12S.GI 1)) (M12SI 2)) (M12S.GI 0),
    bAnd(Nat.beq (pc (pc (M12S.GI 3) (M12S.GI 0)) (M12SI 3)) (M12SI 0),
    Nat.beq (pc (pc (M12S.GI 3) (M12S.GI 1)) (M12SI 3)) (M12SI 1)))))))))) = true := by
  quickRfl

theorem sE : penumSlK 24 5 (mask 5) (24 * 5) true M12S.G M12S.GI 4 M12S.cnt M12S.T M12S.PL
    M12S.POS M12S.SRT M12S.SRI 0 M12S.cnt = true := by quickRfl

theorem sH : slK M12S.cnt (hsortPtK 24 5 (mask 5) M12S.cnt M12S.T M12S.HS M12S.HSI) 0 M12S.cnt =
    true := by quickRfl

theorem sCl : slK (Nat.mul M12S.cnt 8)
    (findPtK M12S.cnt M12S.T (prodQK 24 5 (mask 5) 8 M12S.T (bothK 4 M12S.GI M12SI)) M12Cl) 0
    (Nat.mul M12S.cnt 8) = true := by quickRfl

end CertificateChecks.KernelSpor.M12Syl

end
