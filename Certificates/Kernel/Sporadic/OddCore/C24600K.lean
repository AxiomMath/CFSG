module

public import Certificates.Kernel.Sporadic.OddCore.J2CnK
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.C246BT CFSG.EvenSporadicStandard.Fin76b.Beta.j2BetaHex

#kmisc_hexflat CertificateChecks.KernelSpor.C246BT CFSG.EvenSporadicStandard.Fin76b.Beta.j2BetaHex
  3 315 9 13

namespace CertificateChecks.KernelSpor.C24600

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 315
meta def invA (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 315 a
meta def bM : Array Nat := natArr (j2BetaTbl 7)
meta def biM : Array (Array Nat) := #[invA bM]
meta def pgM : Array (Array Nat) :=
  #[(CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[0]!,
    (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[1]!]
meta def pgiM : Array (Array Nat) := pgM.map invA
meta def conjM : Array (Array Nat) :=
  CFSG.Sporadic.Schreier.PairNative.j2StrongArrs () ++
    (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ()).map invA
meta def wordM (w : List Nat) : Array Nat := w.foldl (fun g l => comp 315 g conjM[l]!) idM
meta def sub8M : Array (Array Nat) := #[wordM [10, 8, 11, 6, 4], wordM [10, 8, 5, 4, 3]]
meta def sub27M : Array (Array Nat) :=
  #[wordM [10, 6, 3], wordM [11, 13, 9, 0, 1], wordM [9, 7, 12, 6, 8, 0, 6]]
meta def sub5M : Array (Array Nat) := #[wordM [8, 7, 12, 11, 6, 1]]
meta def ids (k : Nat) : Array (Array Nat) := Array.replicate k idM
meta def ids1M : Array (Array Nat) := ids 1
meta def ids2M : Array (Array Nat) := ids 2
meta def ids3M : Array (Array Nat) := ids 3
meta def recM (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 idM gs[j]! t) gs.size idM 40).tabs
meta def clM (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recM gs).map fun x => (gs ++ gs.map invA).map fun g => comp 315 x g).flatten
meta def rec8M : Array (Array Nat) := recM sub8M
meta def rec27M : Array (Array Nat) := recM sub27M
meta def rec5M : Array (Array Nat) := recM sub5M
meta def cl8M : Array (Array Nat) := clM sub8M
meta def cl27M : Array (Array Nat) := clM sub27M
meta def cl5M : Array (Array Nat) := clM sub5M
meta def inv8M : Array (Array Nat) := sub8M.map invA
meta def inv27M : Array (Array Nat) := sub27M.map invA
meta def inv5M : Array (Array Nat) := sub5M.map invA

end CertificateChecks.KernelSpor.C24600

open CertificateChecks.KernelSpor.C24600 in
#kmulh CertificateChecks.KernelSpor.C246B 315 9 pgM pgiM bM 1000
open CertificateChecks.KernelSpor.C24600 in
#kmisc_packarrs CertificateChecks.KernelSpor.C246BI biM 9
open CertificateChecks.KernelSpor.C24600 in
#kmulh CertificateChecks.KernelSpor.C246S8 315 9 ids2M sub8M idM 40
open CertificateChecks.KernelSpor.C24600 in
#kmulh CertificateChecks.KernelSpor.C246S27 315 9 ids3M sub27M idM 40
open CertificateChecks.KernelSpor.C24600 in
#kmulh CertificateChecks.KernelSpor.C246S5 315 9 ids1M sub5M idM 40
open CertificateChecks.KernelSpor.C24600 in
#kmisc_packarrs CertificateChecks.KernelSpor.C246S8I inv8M 9
open CertificateChecks.KernelSpor.C24600 in
#kmisc_packarrs CertificateChecks.KernelSpor.C246S27I inv27M 9
open CertificateChecks.KernelSpor.C24600 in
#kmisc_packarrs CertificateChecks.KernelSpor.C246S5I inv5M 9
open CertificateChecks.KernelSpor.C24600 in
#kfind CertificateChecks.KernelSpor.C246S8Cl rec8M cl8M
open CertificateChecks.KernelSpor.C24600 in
#kfind CertificateChecks.KernelSpor.C246S27Cl rec27M cl27M
open CertificateChecks.KernelSpor.C24600 in
#kfind CertificateChecks.KernelSpor.C246S5Cl rec5M cl5M

namespace CertificateChecks.KernelSpor.C24600

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 315 9 (mask 9) (315 * 9) p

@[expose] noncomputable def bK : Nat := C246BT.F 7

@[expose] noncomputable def subGensK (k : Nat) (G GI GJ : Nat → Nat) : Bool :=
  allN k (fun j => bAnd(Nat.beq (G j) idK, bAnd(cK (GI j), bAnd(cK (GJ j),
    bAnd(invEqK 315 9 (mask 9) (315 * 9) (GI j) (GJ j), bAnd(sK (GI j), commK bK (GI j)))))))

theorem k_base : bAnd(cK bK, bAnd(cK (C246BI 0), bAnd(invEqK 315 9 (mask 9) (315 * 9) bK (C246BI 0),
    bAnd(Nat.beq C246B.R bK,
    bAnd(allN 2 (fun j => bAnd(Nat.beq (C246B.G j) (J2P.S j), Nat.beq (C246B.GI j) (J2P.SI j))),
    bAnd(Nat.beq C246B.cnt 560, bAnd(penumHdK C246B.R C246B.cnt 1000 C246B.T C246B.PL,
    bAnd(subGensK 2 C246S8.G C246S8.GI C246S8I, bAnd(Nat.beq C246S8.cnt 8,
    bAnd(penumHdK idK C246S8.cnt 40 C246S8.T C246S8.PL,
    bAnd(subGensK 3 C246S27.G C246S27.GI C246S27I, bAnd(Nat.beq C246S27.cnt 27,
    bAnd(penumHdK idK C246S27.cnt 40 C246S27.T C246S27.PL,
    bAnd(subGensK 1 C246S5.G C246S5.GI C246S5I, bAnd(Nat.beq C246S5.cnt 5,
    penumHdK idK C246S5.cnt 40 C246S5.T C246S5.PL))))))))))))))) = true := by
  quickRfl

theorem k_sq : bAnd(Nat.beq J2C1.cnt 240,
    allN J2C1.cnt (fun i => bIf(Nat.beq (pc (J2C1.T i) (J2C1.T i)) (F 17), false, true))) =
      true := by
  quickRfl

theorem bE : penumSlK 315 9 (mask 9) (315 * 9) true C246B.G C246B.GI 2 C246B.cnt C246B.T C246B.PL
    C246B.POS C246B.SRT C246B.SRI 0 C246B.cnt = true := by quickRfl
theorem bH : slK C246B.cnt (hsortPtK 315 9 (mask 9) C246B.cnt C246B.T C246B.HS C246B.HSI) 0
    C246B.cnt = true := by quickRfl

theorem s8E : penumSlK 315 9 (mask 9) (315 * 9) true C246S8.G C246S8.GI 2 C246S8.cnt C246S8.T
    C246S8.PL C246S8.POS C246S8.SRT C246S8.SRI 0 C246S8.cnt = true := by quickRfl
theorem s8H : slK C246S8.cnt (hsortPtK 315 9 (mask 9) C246S8.cnt C246S8.T C246S8.HS C246S8.HSI) 0
    C246S8.cnt = true := by quickRfl
theorem s8Cl : slK (Nat.mul C246S8.cnt 4)
    (findPtK C246S8.cnt C246S8.T (prodQK 315 9 (mask 9) 4 C246S8.T (bothK 2 C246S8.GI C246S8I))
      C246S8Cl) 0 (Nat.mul C246S8.cnt 4) = true := by quickRfl

theorem s27E : penumSlK 315 9 (mask 9) (315 * 9) true C246S27.G C246S27.GI 3 C246S27.cnt C246S27.T
    C246S27.PL C246S27.POS C246S27.SRT C246S27.SRI 0 C246S27.cnt = true := by quickRfl
theorem s27H : slK C246S27.cnt
    (hsortPtK 315 9 (mask 9) C246S27.cnt C246S27.T C246S27.HS C246S27.HSI) 0 C246S27.cnt = true := by
  quickRfl
theorem s27Cl : slK (Nat.mul C246S27.cnt 6)
    (findPtK C246S27.cnt C246S27.T
      (prodQK 315 9 (mask 9) 6 C246S27.T (bothK 3 C246S27.GI C246S27I)) C246S27Cl) 0
      (Nat.mul C246S27.cnt 6) = true := by quickRfl

theorem s5E : penumSlK 315 9 (mask 9) (315 * 9) true C246S5.G C246S5.GI 1 C246S5.cnt C246S5.T
    C246S5.PL C246S5.POS C246S5.SRT C246S5.SRI 0 C246S5.cnt = true := by quickRfl
theorem s5H : slK C246S5.cnt (hsortPtK 315 9 (mask 9) C246S5.cnt C246S5.T C246S5.HS C246S5.HSI) 0
    C246S5.cnt = true := by quickRfl
theorem s5Cl : slK (Nat.mul C246S5.cnt 2)
    (findPtK C246S5.cnt C246S5.T (prodQK 315 9 (mask 9) 2 C246S5.T (bothK 1 C246S5.GI C246S5I))
      C246S5Cl) 0 (Nat.mul C246S5.cnt 2) = true := by quickRfl

end CertificateChecks.KernelSpor.C24600

end
