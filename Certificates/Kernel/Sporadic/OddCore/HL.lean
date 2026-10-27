module

public import Certificates.Kernel.Sporadic.He.Bind2112
public import Certificates.Kernel.Sporadic.OddCore.PEnumFamCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SmallOddCore.HeLocalCheckInputs
public import CFSG.Sporadic.HeldB.InnerData
meta import CFSG.Sporadic.SmallOddCore.HeLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeL

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.HeldB

meta def omM : List Nat := heOmega0.toList
meta def kgM : Array (Array Nat) := heKGens
meta def kiM : Array (Array Nat) := heKInvs
meta def dgM : Array (Array Nat) := heDGens
meta def diM : Array (Array Nat) := heDInvs
meta def id105 : Array Nat := idTab 105
meta def repsM : Array (Array Nat) :=
  (List.range 10).toArray.map fun l => wordTabS 105 heDGens (heDClassWords.getD l [])

meta def normPosM (first : Bool) : Array (Array Nat) :=
  let idx := indexOf heDEnum.tabs
  ((List.range 9).toArray.map fun j => (List.range 5).toArray.map fun i =>
    let x := if first then conjTab 105 heKGens[j]! heKInvs[j]! heDGens[i]!
      else conjTab 105 heKInvs[j]! heKGens[j]! heDGens[i]!
    #[idx.getD x 0]).flatten

meta def normPos1M : Array (Array Nat) := normPosM true
meta def normPos2M : Array (Array Nat) := normPosM false

meta def coverM : Array (Array Nat) :=
  let idxs := heDOrbits.map fun e => indexOf e.tabs
  heDEnum.tabs.map fun t =>
    let l := ((List.range 10).find? fun l => (idxs[l]!).contains t).getD 0
    #[65536 * l + (idxs[l]!).getD t 0]

end CertificateChecks.KernelSpor.HeL

#knatlist CertificateChecks.KernelSpor.HeL.omL CertificateChecks.KernelSpor.HeL.omM
#kpenum CertificateChecks.KernelSpor.HKE 105 7 false CertificateChecks.KernelSpor.HeL.kgM
  CertificateChecks.KernelSpor.HeL.kgM CertificateChecks.KernelSpor.HeL.id105 40320
#kmisc_packarrs CertificateChecks.KernelSpor.HKI CertificateChecks.KernelSpor.HeL.kiM 7
#kpenum CertificateChecks.KernelSpor.HDE 105 7 false CertificateChecks.KernelSpor.HeL.dgM
  CertificateChecks.KernelSpor.HeL.dgM CertificateChecks.KernelSpor.HeL.id105 20160
#kmisc_packarrs CertificateChecks.KernelSpor.HDI CertificateChecks.KernelSpor.HeL.diM 7
#kpenumfam CertificateChecks.KernelSpor.HOF 105 7 true CertificateChecks.KernelSpor.HeL.dgM
  CertificateChecks.KernelSpor.HeL.diM CertificateChecks.KernelSpor.HeL.repsM 5000
#kmisc_packarrs CertificateChecks.KernelSpor.HNP1 CertificateChecks.KernelSpor.HeL.normPos1M 32
#kmisc_packarrs CertificateChecks.KernelSpor.HNP2 CertificateChecks.KernelSpor.HeL.normPos2M 32
#kmisc_packarrs CertificateChecks.KernelSpor.HCOV CertificateChecks.KernelSpor.HeL.coverM 32

namespace CertificateChecks.KernelSpor.HeL

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Mathieu CFSG.KC.Misc.HexAt CFSG.Sporadic.HeldB

@[expose] noncomputable def letK (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun n => nIf(Nat.beq n (nat_lit 2), CertificateChecks.KernelSpor.HeC.S 1,
      CertificateChecks.KernelSpor.HeC.S 0))
    (fun m => nIf(Nat.beq m (nat_lit 1), CertificateChecks.KernelSpor.HeC.SI 1,
      CertificateChecks.KernelSpor.HeC.SI 0)) l

@[expose] noncomputable def hwpt (wd : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (ih x) (fun y => pg 14 (mask 14) (letK l) y)) wd x

@[expose] noncomputable def wK (j : Nat) : List Int := heInnerWords0.getD j []

@[expose] noncomputable def sigK (j : Nat) : Bool :=
  bAnd(canonK 105 7 (mask 7) (105 * 7) (HKE.G j),
  bAnd(invEqK 105 7 (mask 7) (105 * 7) (HKE.G j) (HKI j),
  bAnd(invEqK 105 7 (mask 7) (105 * 7) (HKI j) (HKE.G j),
  bAnd(canonK 105 7 (mask 7) (105 * 7) (HKI j),
  bAnd(Nat.beq (pcomp 105 7 (mask 7) (HKI j) (HKE.G j)) (pidn 105 7),
    allN 105 (fun k => Nat.beq (hwpt (wK j) (nget omL k))
      (nget omL (pg 7 (mask 7) (HKE.G j) k))))))))

theorem sig0 : sigK 0 = true := by quickRfl
theorem sig1 : sigK 1 = true := by quickRfl
theorem sig2 : sigK 2 = true := by quickRfl
theorem sig3 : sigK 3 = true := by quickRfl
theorem sig4 : sigK 4 = true := by quickRfl
theorem sig5 : sigK 5 = true := by quickRfl
theorem sig6 : sigK 6 = true := by quickRfl
theorem sig7 : sigK 7 = true := by quickRfl
theorem sig8 : sigK 8 = true := by quickRfl

theorem base_ok : bAnd(szOK 105 7, bAnd(canonK 105 7 (mask 7) (105 * 7) (pidn 105 7),
    bAnd(CFSG.KS.Prim.idK 105 7 (mask 7),
    allN 2 (fun k => bAnd(
      canonK 8330 14 (mask 14) (8330 * 14) (CertificateChecks.KernelSpor.HeC.S k),
      canonK 8330 14 (mask 14) (8330 * 14) (CertificateChecks.KernelSpor.HeC.SI k)))))) = true := by
  quickRfl

theorem dg_ok : allN 5 (fun i => bAnd(Nat.beq (HDE.G i)
      (wordTabK 105 7 (mask 7) (pidn 105 7) HKE.G (lget2 heDWords i)),
    bAnd(canonK 105 7 (mask 7) (105 * 7) (HDE.G i),
    bAnd(invEqK 105 7 (mask 7) (105 * 7) (HDE.G i) (HDI i),
    bAnd(invEqK 105 7 (mask 7) (105 * 7) (HDI i) (HDE.G i),
    bAnd(canonK 105 7 (mask 7) (105 * 7) (HDI i),
      Nat.beq (pcomp 105 7 (mask 7) (HDI i) (HDE.G i)) (pidn 105 7))))))) = true := by
  quickRfl

theorem fam_g : allN 5 (fun k => bAnd(Nat.beq (HOF.G k) (HDE.G k), Nat.beq (HOF.GI k) (HDI k))) =
    true := by
  quickRfl

theorem heads : bAnd(penumHdK (pidn 105 7) HKE.cnt 40320 HKE.T HKE.PL,
    penumHdK (pidn 105 7) HDE.cnt 20160 HDE.T HDE.PL) = true := by
  quickRfl

@[expose] noncomputable def orbHd (l : Nat) : Bool :=
  penumHdK (HOF.R l) (HOF.C l) 5000 (offF HOF.T (HOF.TO l)) (offF HOF.PL (HOF.PLO l))

theorem orb_hds : allN 10 orbHd = true := by quickRfl

theorem reps_ok : allN 10 (fun l => bAnd(Nat.beq (HOF.R l)
    (wordTabK 105 7 (mask 7) (pidn 105 7) HDE.G (lget2 heDClassWords l)),
    Nat.beq (HOF.C l) (nget heDClassSizes l))) = true := by
  quickRfl

theorem notin : allN 10 (fun l => allN 10 (fun l' => bIf(Nat.beq l l', true,
    allN (HOF.C l) (fun q => bIf(Nat.beq (offF HOF.T (HOF.TO l) q) (HOF.R l'), false, true))))) =
    true := by
  quickRfl

theorem d_norm : allN 9 (fun j => allN 5 (fun i =>
    bAnd(strictB (HNP1 (Nat.add (Nat.mul j 5) i)) (fun q => bAnd(Nat.blt q HDE.cnt,
      Nat.beq (HDE.T q) (pcomp 105 7 (mask 7) (pcomp 105 7 (mask 7) (HKE.G j) (HDE.G i)) (HKI j)))),
    strictB (HNP2 (Nat.add (Nat.mul j 5) i)) (fun q => bAnd(Nat.blt q HDE.cnt,
      Nat.beq (HDE.T q) (pcomp 105 7 (mask 7) (pcomp 105 7 (mask 7) (HKI j) (HDE.G i))
        (HKE.G j))))))) = true := by
  quickRfl

@[expose] noncomputable def coverK (k : Nat) : Bool :=
  strictB (HCOV k) (fun wk =>
    strictB (Nat.shiftRight wk 16) (fun l => strictB (Nat.land wk 65535) (fun q =>
      bAnd(Nat.blt l 10, bAnd(Nat.blt q (HOF.C l),
        Nat.beq (offF HOF.T (HOF.TO l) q) (HDE.T k))))))

theorem cover0 : allBlk 0 coverK 10080 = true := by quickRfl
theorem cover1 : allBlk 10080 coverK 10080 = true := by quickRfl

end CertificateChecks.KernelSpor.HeL

end
