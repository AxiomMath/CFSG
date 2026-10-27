module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.IrrSylowK
public import CFSG.Sporadic.SmallOddCore.M12IrrInputs
meta import CFSG.Sporadic.SmallOddCore.M12IrrInputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.M12Irr

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 24

meta def ids3M : Array (Array Nat) := Array.replicate 3 idM

meta def sM : Array (Array Nat) := m12IrrSylowTbls.toArray.map natArr

meta def siM : Array (Array Nat) := sM.map (CFSG.Monster.B.Co2.Native.invCand 24)

meta def lM : Array (Array Nat) :=
  let g := #[natArr m12A1Tbl, natArr m12B1Tbl, natArr m12SigmaTbl]
  g ++ g.map (CFSG.Monster.B.Co2.Native.invCand 24)

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 24 idM sM[j]! t) 3 idM 200).tabs

meta def clM : Array (Array Nat) := (recM.map fun x => (sM ++ siM).map fun g => comp 24 x g).flatten

end CertificateChecks.KernelSpor.M12Irr

#kmulh CertificateChecks.KernelSpor.M12IS 24 5 CertificateChecks.KernelSpor.M12Irr.ids3M
  CertificateChecks.KernelSpor.M12Irr.sM CertificateChecks.KernelSpor.M12Irr.idM 200
#kmisc_packarrs CertificateChecks.KernelSpor.M12ISI CertificateChecks.KernelSpor.M12Irr.siM 5
#kmisc_packarrs CertificateChecks.KernelSpor.M12IL CertificateChecks.KernelSpor.M12Irr.lM 5
#kfind CertificateChecks.KernelSpor.M12ICl CertificateChecks.KernelSpor.M12Irr.recM
  CertificateChecks.KernelSpor.M12Irr.clM

namespace CertificateChecks.KernelSpor.M12Irr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.IrrK
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 24 5 (mask 5) (24 * 5) p

@[expose] noncomputable def lS (l : Nat) : Nat := M12IL (Nat.sub l 1)

theorem tabs_eq : natArr m12A1Tbl = unpack 24 5 (M12IL 0) ∧
    natArr m12B1Tbl = unpack 24 5 (M12IL 1) ∧ natArr m12SigmaTbl = unpack 24 5 (M12IL 2) := by
  decide +kernel

theorem base_ok : bAnd(szOK 24 5, bAnd(cK (pidn 24 5), bAnd(CFSG.KS.Prim.idK 24 5 (mask 5),
    bAnd(allN 6 (fun j => cK (M12IL j)), bAnd(allN 3 (fun j => cK (M12ISI j)),
    bAnd(invEqK 24 5 (mask 5) (24 * 5) (M12IL 0) (M12IL 3),
    bAnd(invEqK 24 5 (mask 5) (24 * 5) (M12IL 1) (M12IL 4),
    bAnd(invEqK 24 5 (mask 5) (24 * 5) (M12IL 2) (M12IL 5),
    bAnd(allN 3 (fun j => invEqK 24 5 (mask 5) (24 * 5) (M12IS.GI j) (M12ISI j)),
    bAnd(allN 3 (fun j => Nat.beq (M12IS.G j) (pidn 24 5)),
    bAnd(allN 3 (fun j => Nat.beq (M12IS.GI j)
      (wfoldK 24 5 (mask 5) lS (m12IrrSylowWords.getD j []) (pidn 24 5))),
    bAnd(Nat.beq M12IS.cnt 128, penumHdK (pidn 24 5) M12IS.cnt 200 M12IS.T M12IS.PL)))))))))))) =
      true := by
  quickRfl

theorem sE : penumSlK 24 5 (mask 5) (24 * 5) true M12IS.G M12IS.GI 3 M12IS.cnt M12IS.T M12IS.PL
    M12IS.POS M12IS.SRT M12IS.SRI 0 M12IS.cnt = true := by quickRfl

theorem sH : slK M12IS.cnt (hsortPtK 24 5 (mask 5) M12IS.cnt M12IS.T M12IS.HS M12IS.HSI) 0
    M12IS.cnt = true := by quickRfl

theorem sCl : slK (Nat.mul M12IS.cnt 6)
    (findPtK M12IS.cnt M12IS.T (prodQK 24 5 (mask 5) 6 M12IS.T (bothK 3 M12IS.GI M12ISI)) M12ICl) 0
    (Nat.mul M12IS.cnt 6) = true := by quickRfl

@[expose] noncomputable def ES : List Nat := (List.range M12IS.cnt).map M12IS.T

@[expose] noncomputable def sK (b : Nat) : Bool := Nat.blt (pg 5 (mask 5) b 0) 12

theorem k_cand : candP 24 5 ES [] = true := by quickRfl

theorem k_irr : irrP 24 5 sK ES [] = true := by quickRfl

end CertificateChecks.KernelSpor.M12Irr

end
