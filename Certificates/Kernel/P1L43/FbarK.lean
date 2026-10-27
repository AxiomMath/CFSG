module

public import Certificates.Kernel.P1L43.FbarD
public import Certificates.Kernel.SchreierFam.L43Chain
public import Certificates.Data.Kernel.U43Case
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.K442264

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.U43Case
open CertificateChecks.KernelP1L43 CFSG.ComponentClassification.HarrisLit.P1.L43
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.KC.Misc.ArrEnum
open Certificates.Asc82Fbar

@[expose] noncomputable def fb442cn (x : Nat) : Bool := canonK 80 7 (mask 7) (80 * 7) x

@[expose] noncomputable def fb442invS (p r : Nat) : Bool :=
  bAnd(fb442cn p, bAnd(fb442cn r, invEqK 80 7 (mask 7) (80 * 7) p r))

@[expose] noncomputable def fb442inv2 (x : Nat) : Bool :=
  bAnd(Nat.beq (pp 80 7 x x) (pidn 80 7), bIf(Nat.beq x (pidn 80 7), false, true))

@[expose] noncomputable def fb442RecB (k cnt RK RC : Nat) (T PL G GI GJ : Nat → Nat) : Bool :=
  bAnd(Nat.beq RK k, bAnd(Nat.beq RC cnt, bAnd(penumHdK (pidn 80 7) RC 100000 T PL,
    allN k (fun j => bAnd(Nat.beq (G j) (pidn 80 7), fb442invS (GI j) (GJ j))))))

@[expose] def fb442cdL : List Nat :=
  [15, 16, 17, 21, 22, 23, 28, 31, 34, 37, 41, 42, 46, 48, 53, 56, 59, 62, 65, 67, 69, 74, 75, 79]

@[expose] def fb442cd (j : Nat) : Nat := fb442cdL.getD j 0

@[expose] def fb442cmul (x y : Nat) : Nat :=
  27 * ((x / 27 % 3 * (y / 27 % 3) % 3 + x / 9 % 3 * (y / 3 % 3) % 3) % 3) +
    9 * ((x / 27 % 3 * (y / 9 % 3) % 3 + x / 9 % 3 * (y % 3) % 3) % 3) +
    3 * ((x / 3 % 3 * (y / 27 % 3) % 3 + x % 3 * (y / 3 % 3) % 3) % 3) +
    (x / 3 % 3 * (y / 9 % 3) % 3 + x % 3 * (y % 3) % 3) % 3

@[expose] noncomputable def fb442cj (j : Nat) : Nat := pp 80 7 (pp 80 7 (FB 1) (FI.GI j)) (FB 2)

@[expose] noncomputable def fb442cjI (j : Nat) : Nat := pp 80 7 (pp 80 7 (FB 1) (FII j)) (FB 2)

@[expose] noncomputable def fb442qC (i : Nat) : Bool :=
  bAnd(commP 80 7 (FI.T i) (FB 0), bAnd(commP 80 7 (FI.T i) (fb442cj 0),
    commP 80 7 (FI.T i) (fb442cj 1)))

theorem fb442idK : fb442invS (pidn 80 7) (pidn 80 7) = true := by quickRfl

theorem fb442headI : fb442RecB 2 360 FI.k FI.cnt FI.T FI.PL FI.G FI.GI FII = true := by quickRfl
theorem fb442headO : fb442RecB 2 360 FO.k FO.cnt FO.T FO.PL FO.G FO.GI FOI = true := by quickRfl
theorem fb442headR : fb442RecB 2 8 FR.k FR.cnt FR.T FR.PL FR.G FR.GI FRI = true := by quickRfl
theorem fb442headM : fb442RecB 2 288 FM.k FM.cnt FM.T FM.PL FM.G FM.GI FMI = true := by quickRfl
theorem fb442headK : fb442RecB 24 24 FK.k FK.cnt FK.T FK.PL FK.G FK.GI FKI = true := by quickRfl

@[expose] noncomputable def fb442peI (k : Nat) : Bool :=
  penumSlK 80 7 (mask 7) (80 * 7) true FI.G FI.GI 2 FI.cnt FI.T FI.PL FI.POS FI.SRT FI.SRI
    (Nat.mul 120 k) 120
@[expose] noncomputable def fb442peO (k : Nat) : Bool :=
  penumSlK 80 7 (mask 7) (80 * 7) true FO.G FO.GI 2 FO.cnt FO.T FO.PL FO.POS FO.SRT FO.SRI
    (Nat.mul 120 k) 120
@[expose] noncomputable def fb442peR (k : Nat) : Bool :=
  penumSlK 80 7 (mask 7) (80 * 7) true FR.G FR.GI 2 FR.cnt FR.T FR.PL FR.POS FR.SRT FR.SRI
    (Nat.mul 8 k) 8
@[expose] noncomputable def fb442peM (k : Nat) : Bool :=
  penumSlK 80 7 (mask 7) (80 * 7) true FM.G FM.GI 2 FM.cnt FM.T FM.PL FM.POS FM.SRT FM.SRI
    (Nat.mul 96 k) 96
@[expose] noncomputable def fb442peK (k : Nat) : Bool :=
  penumSlK 80 7 (mask 7) (80 * 7) true FK.G FK.GI 24 FK.cnt FK.T FK.PL FK.POS FK.SRT FK.SRI
    (Nat.mul 24 k) 24

@[expose] noncomputable def fb442hsI (k : Nat) : Bool :=
  slK FI.cnt (hsortPtK 80 7 (mask 7) FI.cnt FI.T FI.HS FI.HSI) (Nat.mul 360 k) 360
@[expose] noncomputable def fb442hsO (k : Nat) : Bool :=
  slK FO.cnt (hsortPtK 80 7 (mask 7) FO.cnt FO.T FO.HS FO.HSI) (Nat.mul 360 k) 360
@[expose] noncomputable def fb442hsR (k : Nat) : Bool :=
  slK FR.cnt (hsortPtK 80 7 (mask 7) FR.cnt FR.T FR.HS FR.HSI) (Nat.mul 8 k) 8
@[expose] noncomputable def fb442hsM (k : Nat) : Bool :=
  slK FM.cnt (hsortPtK 80 7 (mask 7) FM.cnt FM.T FM.HS FM.HSI) (Nat.mul 288 k) 288
@[expose] noncomputable def fb442hsK (k : Nat) : Bool :=
  slK FK.cnt (hsortPtK 80 7 (mask 7) FK.cnt FK.T FK.HS FK.HSI) (Nat.mul 24 k) 24

@[expose] noncomputable def fb442clI (k : Nat) : Bool :=
  slK (Nat.mul FI.cnt 4) (findPtK FI.cnt FI.T (prodQK 80 7 (mask 7) 4 FI.T (bothK 2 FI.GI FII))
    FICl) (Nat.mul 360 k) 360
@[expose] noncomputable def fb442clO (k : Nat) : Bool :=
  slK (Nat.mul FO.cnt 4) (findPtK FO.cnt FO.T (prodQK 80 7 (mask 7) 4 FO.T (bothK 2 FO.GI FOI))
    FOCl) (Nat.mul 360 k) 360
@[expose] noncomputable def fb442clR (k : Nat) : Bool :=
  slK (Nat.mul FR.cnt 4) (findPtK FR.cnt FR.T (prodQK 80 7 (mask 7) 4 FR.T (bothK 2 FR.GI FRI))
    FRCl) (Nat.mul 32 k) 32
@[expose] noncomputable def fb442clK (k : Nat) : Bool :=
  slK (Nat.mul FK.cnt 48) (findPtK FK.cnt FK.T
    (prodQK 80 7 (mask 7) 48 FK.T (bothK 24 FK.GI FKI)) FKCl) (Nat.mul 288 k) 288

@[expose] noncomputable def fb442wit (cnt : Nat) (T W : Nat → Nat) (b i : Nat) : Bool :=
  bIf(fb442inv2 (T i), strictB (r32 W i) (fun j => bAnd(Nat.blt j cnt,
    Nat.beq (pp 80 7 (T i) (T j)) (pp 80 7 (T j) b))), true)

@[expose] noncomputable def fb442wtI (k : Nat) : Bool :=
  slK FI.cnt (fb442wit FI.cnt FI.T FIW (FB 0)) (Nat.mul 360 k) 360
@[expose] noncomputable def fb442wtO (k : Nat) : Bool :=
  slK FO.cnt (fb442wit FO.cnt FO.T FOW (FB 6)) (Nat.mul 360 k) 360

@[expose] noncomputable def fb442inn : Bool :=
  bAnd(allN 10 (fun j => fb442cn (FB j)),
  bAnd(fb442invS (FB 0) (FB 0), bAnd(fb442inv2 (FB 0),
  bAnd(findPtK FI.cnt FI.T (fun _ => FB 0) FIx 0,
  bAnd(fb442invS (FB 1) (FB 2),
  bAnd(Nat.beq (pp 80 7 (FB 1) (FB 5)) (pp 80 7 (FB 0) (FB 1)),
  bAnd(fb442invS (fb442cj 0) (fb442cjI 0), bAnd(fb442invS (fb442cj 1) (fb442cjI 1),
  bAnd(Nat.ble (cntBelowK FI.cnt fb442qC 6) 2,
  bAnd(fb442invS (FB 3) (FB 3), bAnd(fb442inv2 (FB 3), bAnd(commP 80 7 (FB 3) (FB 0),
  bAnd(findPtK FI.cnt FI.T (fun _ => FB 3) FIx 1,
  bAnd(fb442invS (FB 4) (FB 4), bAnd(fb442inv2 (FB 4), bAnd(commP 80 7 (FB 4) (FB 0),
  bAnd(findPtK FI.cnt FI.T (fun _ => FB 4) FIx 2,
  bAnd(Nat.beq (FR.GI 0) (FB 3), Nat.beq (FR.GI 1) (FB 4)))))))))))))))))))

@[expose] noncomputable def fb442out : Bool :=
  bAnd(fb442invS (FB 6) (FB 6), bAnd(fb442inv2 (FB 6),
  bAnd(findPtK FO.cnt FO.T (fun _ => FB 6) FOx 0,
  bAnd(fb442invS (FB 7) (FB 8),
  bAnd(Nat.beq (pp 80 7 (FB 7) (FB 9)) (pp 80 7 (FB 6) (FB 7)),
  bAnd(allN 24 (fun i => allN 24 (fun j => strictB (r32 FKT (Nat.add (Nat.mul 24 i) j)) (fun m =>
    bAnd(Nat.blt m 24, bAnd(Nat.beq (pp 80 7 (FK.GI i) (FK.GI j)) (FK.GI m),
      Nat.beq (fb442cd m) (fb442cmul (fb442cd i) (fb442cd j))))))),
  bAnd(allN 24 (fun i => bIf(Nat.beq (FK.GI i) (pidn 80 7), Nat.beq (fb442cd i) 28, true)),
  bAnd(Nat.beq (FK.GI 15) (FB 9),
  bAnd(allN 24 (findPtK FM.cnt FM.T FK.GI FMx),
    slK (Nat.mul FK.cnt 2) (findPtK FK.cnt FK.T (conjQK 80 7 (mask 7) 2 FK.T FM.GI FMI) FKN)
      0 48)))))))))

theorem fb442innK : fb442inn = true := by quickRfl
theorem fb442outK : fb442out = true := by quickRfl

theorem fb442binds :
    arrBind (natArr (tm 22222087)) 80 7 (FI.GI 0) = true ∧
    arrBind (natArr (tm 30806896)) 80 7 (FI.GI 1) = true ∧
    arrBind (natArr (tm 28947042)) 80 7 (FO.GI 0) = true ∧
    arrBind (natArr (tm 5634355)) 80 7 (FO.GI 1) = true ∧
    arrBind (natArr (tm 18085123)) 80 7 (FM.GI 0) = true ∧
    arrBind (natArr (tm 27169507)) 80 7 (FM.GI 1) = true ∧
    arrBind (natArr (tm 37301281)) 80 7 (FB 0) = true ∧
    arrBind (natArr (tm 38099616)) 80 7 (FB 1) = true ∧
    arrBind (natArr (tm 23098396)) 80 7 (FB 3) = true ∧
    arrBind (natArr (tm 11712909)) 80 7 (FB 4) = true ∧
    arrBind (natArr (tm 11821474)) 80 7 (FB 5) = true ∧
    arrBind (natArr (tm 19250485)) 80 7 (FB 6) = true ∧
    arrBind (natArr (tm 31901178)) 80 7 (FB 7) = true ∧
    arrBind (natArr (tm 38855539)) 80 7 (FB 9) = true := by
  decide +kernel

theorem fb442rhoB : allN 24 (fun j =>
    arrBind (natArr ((fbarRho ()).getD (fb442cd j) (idT 80))) 80 7 (FK.GI j)) = true := by
  decide +kernel

theorem fb442rho : (List.range 81).all (fun c => (rhoPairs.lookup c).isNone ||
    fb442cdL.contains c) = true := by
  decide +kernel

theorem fb442sift : CertificateChecks.KernelSchreierFam.L43.siftL43 (tm 38099616) = true ∧
    CertificateChecks.KernelSchreierFam.L43.siftL43 (tm 31901178) = true := by
  decide +kernel

theorem fb442negWit : bIf(fb442wit FI.cnt FI.T FIW (FB 3) (r32 FIx 0), false, true) = true := by
  quickRfl

theorem fb442negHom : bIf(Nat.beq (pp 80 7 (FK.GI 1) (FK.GI 2)) (FK.GI 3), false, true) = true := by
  quickRfl

theorem fb442negCnt :
    bIf(Nat.ble (cntBelowK FI.cnt (fun i => commP 80 7 (FI.T i) (FB 0)) 6) 2, false, true) = true := by
  quickRfl

end CertificateChecks.K442264

end

set_option maxRecDepth 400000
set_option Elab.async false

#kc_each CertificateChecks.K442264.fb442peI 0 3
#kc_each CertificateChecks.K442264.fb442peO 0 3
#kc_each CertificateChecks.K442264.fb442peR 0 1
#kc_each CertificateChecks.K442264.fb442peM 0 3
#kc_each CertificateChecks.K442264.fb442peK 0 1
#kc_each CertificateChecks.K442264.fb442hsI 0 1
#kc_each CertificateChecks.K442264.fb442hsO 0 1
#kc_each CertificateChecks.K442264.fb442hsR 0 1
#kc_each CertificateChecks.K442264.fb442hsM 0 1
#kc_each CertificateChecks.K442264.fb442hsK 0 1
#kc_each CertificateChecks.K442264.fb442clI 0 4
#kc_each CertificateChecks.K442264.fb442clO 0 4
#kc_each CertificateChecks.K442264.fb442clR 0 1
#kc_each CertificateChecks.K442264.fb442clK 0 4
#kc_each CertificateChecks.K442264.fb442wtI 0 1
#kc_each CertificateChecks.K442264.fb442wtO 0 1
