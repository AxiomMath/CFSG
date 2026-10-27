module

public import Certificates.Kernel.HN1408.CzTScanDefs
public import Certificates.Kernel.HN1408.D442204Data
public import Certificates.Kernel.HN1408.M11Lem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5DData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5TData
public import Certificates.Kernel.HN1408.CzTDefs
public import Certificates.Kernel.HN1408.Y442202Rec

public section

namespace CFSG.KD.HN1408.D442204

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.Simple2S5 CFSG.KD.HN1408.CzT

@[expose] noncomputable def sub3 (X₁ X₂ X₃ i : Nat) : Nat :=
  nIf(Nat.beq i 1, X₁, nIf(Nat.beq i 2, X₂, nIf(Nat.beq i 3, X₃, idK)))

@[expose] noncomputable def lwK (X₁ X₂ X₃ : Nat) (l : List Nat) : Nat :=
  l.foldl (fun acc i => pc acc (sub3 X₁ X₂ X₃ i)) idK

@[expose] noncomputable def Y1 : Nat := Y442202.Y0.G 0

@[expose] noncomputable def Y2 : Nat := Y442202.Y0.G 1

@[expose] noncomputable def headK (H : Nat → Nat) : Bool :=
  strictB (WK wordZ) fun Z => strictB (pc (WK wordA) Z) fun T => strictB (H 19) fun G0 =>
    strictB (H 18) fun U =>
      bAnd(Nat.beq U (lwK Y1 Y2 idK (uLetters.getD 0 [])), bAnd(Nat.beq G0 (WK g0Word),
      bAnd(Nat.beq (pc G0 T) (pc U G0),
      bAnd(canonK 1408 11 (mask 11) (1408 * 11) (H 0), bAnd(Nat.beq (pc G0 (H 0)) (pc T G0),
      bAnd(canonK 1408 11 (mask 11) (1408 * 11) (H 1), bAnd(Nat.beq (pc G0 (H 1)) (pc (pc T U) G0),
      bAnd(commP Y1 Z, bAnd(commP Y2 Z,
        allN 16 fun j => strictB (H (Nat.add 2 j)) fun D =>
          bAnd(canonK 1408 11 (mask 11) (1408 * 11) D,
            bAnd(Nat.beq (pc (WK (gWords.getD j [])) D) G0, commP D Z)))))))))))

@[expose] noncomputable def conjB (A B U V g0 g1 : Nat) : Bool :=
  bAnd(Nat.beq (pt A (pt B (pt U 0))) (pt V g0), Nat.beq (pt A (pt B (pt U 1))) (pt V g1))

@[expose] noncomputable def cellK (H : Nat → Nat) (A B F : Nat) : Bool :=
  strictB (pt A (pt B 0)) fun g0 => strictB (pt A (pt B 1)) fun g1 =>
    bIf(bIf(conjB A B (H 18) (H 0) g0 g1, true, conjB A B (H 18) (H 1) g0 g1),
      bIf(Nat.ble 704 (pt (H 19) g0), true,
        bIf(Nat.beq F 0, false,
          strictB (Nat.pred F) fun q => strictB (Nat.div q 240) fun jj =>
            strictB (Nat.mod q 240) fun k =>
              bAnd(Nat.blt jj 16, strictB (H (Nat.add 2 jj)) fun D =>
                strictB (Y442202.Y0.T k) fun Y =>
                  isBase (pt D g0) (pt D g1) (pt Y 0) (pt Y 1)))),
      true)

@[expose] noncomputable def rowK (H : Nat → Nat) (R A : Nat) : Bool :=
  allN 24 fun j => cellK H A (T1 j) (fd R j)

@[expose] noncomputable def covSl (H C : Nat → Nat) (s : Nat) : Bool :=
  allN 64 fun d => strictB (Nat.add (Nat.mul 64 s) d) fun i =>
    strictB (T0 i) fun A => strictB (C i) fun R => rowK H R A

@[expose] noncomputable def covS (s : Nat) : Bool := covSl H C s

@[expose] noncomputable def killK (KD : List (List Nat × Nat)) (j : Nat) : Bool :=
  bIf(Nat.beq j jStar, true,
    strictB (lwK Y1 Y2 (WK (gWords.getD j [])) (KD.getD j ([], 0)).1) fun X =>
      Nat.beq (ppK X (Nat.div (KD.getD j ([], 0)).2 2)) (WK wordA))

@[expose] noncomputable def fixK (p : Nat) : Bool :=
  bAnd(Nat.blt p 1408, bAnd(Nat.beq (pt Y1 p) p, bAnd(Nat.beq (pt Y2 p) p,
    Nat.beq (pt (WK (gWords.getD jStar [])) p) p)))

@[expose] noncomputable def sylGK (G : Nat → Nat) (i k : Nat) : Bool :=
  strictB (WK (gWords.getD jStar [])) fun GS =>
    allN k fun j => Nat.beq (G j) (lwK Y1 Y2 GS ((sylowLetters.getD i []).getD j []))

end CFSG.KD.HN1408.D442204

end
