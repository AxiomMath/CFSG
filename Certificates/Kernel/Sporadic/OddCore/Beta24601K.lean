module

public import Certificates.Kernel.Sporadic.OddCore.S16J2K27810
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.B24601

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 315

meta def idsM : Array (Array Nat) := Array.replicate 2 idM

meta def gM : Array (Array Nat) := #[natArr (j2BetaTbl 8), natArr (j2BetaTbl 9)]

meta def giM : Array (Array Nat) := (gM.push (natArr (j2BetaTbl 7))).map
  (CFSG.Monster.B.Co2.Native.invCand 315)

meta def recM : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 idM gM[j]! t) gM.size idM 1100).tabs

meta def clM : Array (Array Nat) :=
  (recM.map fun x => (gM ++ (giM.extract 0 2)).map fun g => comp 315 x g).flatten

meta def labM : Array (Array Nat) := Id.run do
  let E := bfs (fun j t => conjTab 315 idM gM[j]! t) gM.size idM 1100
  let pg := piGens.map natArr
  let mut r : Array (Array Nat) := #[idTab 6]
  for k in [1:E.tabs.size] do
    r := r.push (comp 6 r[E.par[k]!]! pg[E.lab[k]!]!)
  return r

end CertificateChecks.KernelSpor.B24601

#kmisc_packarrs CertificateChecks.KernelSpor.B24601I CertificateChecks.KernelSpor.B24601.giM 9

#kmisc_packarrs CertificateChecks.KernelSpor.B24601L CertificateChecks.KernelSpor.B24601.labM 3

#kmulh CertificateChecks.KernelSpor.B24601R 315 9 CertificateChecks.KernelSpor.B24601.idsM
  CertificateChecks.KernelSpor.B24601.gM CertificateChecks.KernelSpor.B24601.idM 1100

#kfind CertificateChecks.KernelSpor.B24601Cl CertificateChecks.KernelSpor.B24601.recM
  CertificateChecks.KernelSpor.B24601.clM

namespace CertificateChecks.KernelSpor.B24601

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor.J2Cn CertificateChecks.KernelSpor.S16J2

theorem base_ok : bAnd(szOK 315 9, bAnd(cK idK, bAnd(CFSG.KS.Prim.idK 315 9 (mask 9),
    bAnd(cK (J2BetaT.F 7), bAnd(cK (B24601I 2), bAnd(iK (J2BetaT.F 7) (B24601I 2),
    bAnd(allN 2 (fun j => bAnd(cK (B24601R.GI j), bAnd(cK (B24601I j),
      bAnd(iK (B24601R.GI j) (B24601I j),
      bAnd(Nat.beq (B24601R.GI j) (J2BetaT.F (Nat.add j 8)), bAnd(Nat.beq (B24601R.G j) idK,
      commK (J2BetaT.F 7) (B24601R.GI j))))))),
    bAnd(isId 3 (J2BetaT.F 7), bAnd(notId 1 (J2BetaT.F 7),
    bAnd(sK (J2BetaT.F 8), bAnd(sK (J2BetaT.F 9), bAnd(sK (J2BetaT.F 7),
    bAnd(Nat.beq (J2BetaT.F 8) (F 31),
    bAnd(Nat.beq B24601R.cnt 1080, penumHdK idK B24601R.cnt 1100 B24601R.T B24601R.PL)))))))))))))) =
      true := by
  quickRfl

theorem sE : penumSlK 315 9 (mask 9) (315 * 9) true B24601R.G B24601R.GI 2 B24601R.cnt B24601R.T
    B24601R.PL B24601R.POS B24601R.SRT B24601R.SRI 0 B24601R.cnt = true := by quickRfl

theorem sH : slK B24601R.cnt (hsortPtK 315 9 (mask 9) B24601R.cnt B24601R.T B24601R.HS B24601R.HSI)
    0 B24601R.cnt = true := by quickRfl

theorem sCl : slK (Nat.mul B24601R.cnt 4)
    (findPtK B24601R.cnt B24601R.T (prodQK 315 9 (mask 9) 4 B24601R.T (bothK 2 B24601R.GI B24601I))
      B24601Cl) 0 (Nat.mul B24601R.cnt 4) = true := by quickRfl

@[expose] noncomputable def labT (k : Nat) : Table := tabT (unpack 6 3 (B24601L k))

@[expose] noncomputable def invL6 (x : Table) : Array Nat :=
  (List.range 6).foldl (fun r i => r.set! (x[i]!).toNat i) (Array.replicate 6 0)

@[expose] noncomputable def pK (x : Table) : Bool :=
  (List.range 6).all fun i => decide ((x[i]!).toNat < 6) && (invL6 x)[(x[i]!).toNat]! == i

@[expose] noncomputable def eq6 (x y : Table) : Bool := (List.range 6).all fun i => ap x i == ap y i

@[expose] noncomputable def kerK (y : Nat) : Bool :=
  Nat.beq y idK || Nat.beq y (J2BetaT.F 7) || Nat.beq y (pc (J2BetaT.F 7) (J2BetaT.F 7))

@[expose] noncomputable def cayAt (k : Nat) : Bool :=
  pK (labT k) &&
    (k == 0 || (Nat.blt (parOf B24601R.PL k) k &&
      decide (labT k = compT 6 (labT (parOf B24601R.PL k)) piGens[labOf B24601R.PL k]!))) &&
    (List.range 2).all (fun l => Nat.blt (r32 B24601Cl (4 * k + l)) 1080 &&
      eq6 (labT (r32 B24601Cl (4 * k + l))) (compT 6 (labT k) piGens[l]!)) &&
    (eq6 (labT k) (idT 6) == kerK (B24601R.T k))

@[expose] noncomputable def cayK : Bool :=
  (List.range 1080).all cayAt && decide (labT 0 = idT 6) && piGens.toList.all pK

theorem cay_ok : cayK = true := by
  decide +kernel

theorem cay_neg : ((List.range 1080).all fun k => (List.range 2).all fun l =>
    eq6 (labT (r32 B24601Cl (4 * k + l))) (compT 6 (labT k) piGens[1 - l]!)) = false := by
  decide +kernel

theorem ker_neg : ((List.range 1080).all fun k => eq6 (labT k) (idT 6) ==
    (Nat.beq (B24601R.T k) idK || Nat.beq (B24601R.T k) (J2BetaT.F 7))) = false := by
  decide +kernel

theorem d_neg : Nat.beq (J2BetaT.F 9) (F 31) = false := by
  decide +kernel

end CertificateChecks.KernelSpor.B24601

end
