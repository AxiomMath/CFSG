module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.IrrSylowK
public import CFSG.Sporadic.SmallOddCore.ONIrrInputs
meta import CFSG.Sporadic.SmallOddCore.ONIrrInputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONIrr

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 32

meta def ids6M : Array (Array Nat) := Array.replicate 6 idM

meta def sM : Array (Array Nat) := onIrrSylowTbls.toArray.map natArr

meta def siM : Array (Array Nat) := sM.map (CFSG.Monster.B.Co2.Native.invCand 32)

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 32 idM sM[j]! t) 6 idM 600).tabs

meta def clM : Array (Array Nat) := (recM.map fun x => (sM ++ siM).map fun g => comp 32 x g).flatten

end CertificateChecks.KernelSpor.ONIrr

#kmulh CertificateChecks.KernelSpor.ONIS 32 6 CertificateChecks.KernelSpor.ONIrr.ids6M
  CertificateChecks.KernelSpor.ONIrr.sM CertificateChecks.KernelSpor.ONIrr.idM 600
#kmisc_packarrs CertificateChecks.KernelSpor.ONISI CertificateChecks.KernelSpor.ONIrr.siM 6
#kfind CertificateChecks.KernelSpor.ONICl CertificateChecks.KernelSpor.ONIrr.recM
  CertificateChecks.KernelSpor.ONIrr.clM

namespace CertificateChecks.KernelSpor.ONIrr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.IrrK
open CFSG.ONSchreier.Data

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 32 6 (mask 6) (32 * 6) p

theorem tabs_eq : T32Chain.generators[0]! = unpack 32 6 (ONIS.GI 0) ∧
    T32Chain.generators[1]! = unpack 32 6 (ONIS.GI 1) ∧
    T32Chain.generators[2]! = unpack 32 6 (ONIS.GI 2) ∧
    T32Chain.generators[3]! = unpack 32 6 (ONIS.GI 3) ∧
    T32Chain.generators[4]! = unpack 32 6 (ONIS.GI 4) ∧
    T32Chain.generators[5]! = unpack 32 6 (ONIS.GI 5) := by
  decide +kernel

theorem base_ok : bAnd(szOK 32 6, bAnd(cK (pidn 32 6), bAnd(CFSG.KS.Prim.idK 32 6 (mask 6),
    bAnd(allN 6 (fun j => cK (ONIS.GI j)), bAnd(allN 6 (fun j => cK (ONISI j)),
    bAnd(allN 6 (fun j => invEqK 32 6 (mask 6) (32 * 6) (ONIS.GI j) (ONISI j)),
    bAnd(allN 6 (fun j => Nat.beq (ONIS.G j) (pidn 32 6)),
    bAnd(Nat.beq ONIS.cnt 512, penumHdK (pidn 32 6) ONIS.cnt 600 ONIS.T ONIS.PL)))))))) =
      true := by
  quickRfl

theorem sE : penumSlK 32 6 (mask 6) (32 * 6) true ONIS.G ONIS.GI 6 ONIS.cnt ONIS.T ONIS.PL
    ONIS.POS ONIS.SRT ONIS.SRI 0 ONIS.cnt = true := by quickRfl

theorem sH : slK ONIS.cnt (hsortPtK 32 6 (mask 6) ONIS.cnt ONIS.T ONIS.HS ONIS.HSI) 0
    ONIS.cnt = true := by quickRfl

theorem sCl : slK (Nat.mul ONIS.cnt 12)
    (findPtK ONIS.cnt ONIS.T (prodQK 32 6 (mask 6) 12 ONIS.T (bothK 6 ONIS.GI ONISI)) ONICl) 0
    (Nat.mul ONIS.cnt 12) = true := by quickRfl

@[expose] noncomputable def ES : List Nat := (List.range ONIS.cnt).map ONIS.T

theorem k_cand : candP 32 6 ES [] = true := by quickRfl

theorem k_irr : irrP 32 6 (fun _ => true) ES [] = true := by quickRfl

end CertificateChecks.KernelSpor.ONIrr

end
