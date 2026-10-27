
module

public import CFSG.Monster.B.TwoA.Fischer.CertSieveInputs
public import Certificates.Data.Kernel.MonsterB.FischerK
public import Certificates.Data.Kernel.MonsterB.FischerElim
public import Certificates.Kernel.MonsterB.FischerData3067
public import Certificates.Kernel.MonsterB.IndCandGet

public section

namespace CertificateChecks.KernelMonB.F3067

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Monster.B.Binary.Native
  CFSG.KC.FischerK CFSG.KC.FischerE CFSG.KLie.CT CertificateChecks.KernelMonB.IndCand

@[expose] noncomputable def orbBound : Bool :=
  (List.range 4).all fun i => decide (FD.ORB[i]! < 2 ^ (11 * 2048))

@[expose] noncomputable def oIdx (m : ℕ) : ℕ := fget (FD.ORB[0]!) m 11
@[expose] noncomputable def oDist (m : ℕ) : ℕ := fget (FD.ORB[1]!) m 11
@[expose] noncomputable def oPar (m : ℕ) : ℕ := fget (FD.ORB[2]!) m 11
@[expose] noncomputable def oGen (m : ℕ) : ℕ := fget (FD.ORB[3]!) m 11

@[expose] noncomputable def adL (m : ℕ) : List ℕ :=
  (List.range 78).map fun c => fget (vecMulL FD.ROWS m) c 78

@[expose] noncomputable def rowsChk : Bool :=
  FD.ROWS.length == 78 && (List.range 78).all fun i =>
    (bTableArr[i]!).size == 78 && packW 78 (FD.ROWS[i]!) (bTableArr[i]!).toList 0

@[expose] noncomputable def spanT (L : List ℕ) (r : ℕ) : Bool :=
  allBelow 78 L && Nat.beq (nzL (elimL 77 L (zerosL 78))) r

@[expose] noncomputable def orbitEntryT (m : ℕ) : Bool :=
  decide (oIdx m < 8) &&
    ((List.range 12).all fun k =>
      let x := vecMulL (fColArr[k]!).toList m
      decide (x < 2048) && oIdx x == oIdx m) &&
    (if oDist m = 0 then m == orbRep (oIdx m)
      else decide (oPar m < 2048) && oIdx (oPar m) == oIdx m &&
        oDist (oPar m) + 1 == oDist m && decide (oGen m < 2) &&
        vecMulL (fColArr[oGen m]!).toList (oPar m) == m) &&
    spanT (adL m) (orbRank (oIdx m))

@[expose] noncomputable def orbitRestT : Bool :=
  ((List.range 8).all fun t => oIdx (orbRep t) == t && decide (orbRep t < 2048)) &&
    (List.range 2048).all fun m =>
      (oIdx m == 0) == (m == 0) && (oIdx m == 7) == (m == 949) &&
        (oIdx m == 1) == ((List.range 22).map labelCoord).contains m &&
        (oIdx m == 6) == ((List.range 22).map fun c => 949 ^^^ labelCoord c).contains m

@[expose] noncomputable def invF (k y : ℕ) : ℕ := fget (FD.INV[k]!) y 12

@[expose] noncomputable def invChk (k : ℕ) : Bool :=
  allN 3510 fun y => decide (candF k y < 3510) && invF k (candF k y) == y &&
    decide (invF k y < 3510) && candF k (invF k y) == y

@[expose] noncomputable def labF (w : List ℕ) (x : ℕ) : ℕ :=
  wordL candF w (candF 12 (invWordL invF w x))

@[expose] noncomputable def lcF (y : ℕ) : ℕ := fget (FD.LC[0]!) y 78

@[expose] noncomputable def lcChk : Bool :=
  packW 78 (FD.LC[0]!) labelCoordArr.toList 0 && labelCoordArr.toList.length == 3510 &&
    decide (FD.LC[0]! < 2 ^ (78 * 3510))

@[expose] noncomputable def tableEntryT (w : List ℕ) (i j : ℕ) : Bool :=
  bTable i j == if labF w (basisPt j) = basisPt j then 0
    else lcF (basisPt i) ^^^ lcF (basisPt j) ^^^ lcF (labF w (basisPt j))

@[expose] noncomputable def tableRowT (i : ℕ) : Bool :=
  (labelWord i).all (· < 13) && (List.range 78).all fun j => tableEntryT (labelWord i) i j

end CertificateChecks.KernelMonB.F3067

end
