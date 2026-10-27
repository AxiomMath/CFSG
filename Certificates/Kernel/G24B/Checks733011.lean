module

public import Certificates.Kernel.G24B.Checks733008
public import Certificates.Kernel.G24B.NData
import CFSG.Certificates.Kernel.Common.F2Bfs
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.KC.Misc.G24 CFSG.KC.F2BfsRec CFSG.KLie.CT CFSG.KC.M1F2 CFSG.Quasithin.St84.G24Ident

@[expose] noncomputable def GE : List Nat := [bX 1, bX 2]

end CFSG.KD.G24B

#kc_f2bfs CFSG.KD.G24B.EE 28 CFSG.KD.G24B.GE 4096 6 12

namespace CFSG.KD.G24B

open CFSG.KC.Misc.G24 CFSG.KC.F2BfsRec CFSG.KLie.CT CFSG.KC.M1F2 CFSG.Quasithin.St84.G24Ident

@[expose] noncomputable def pcK (G : List Nat) (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (oneF2 28)
    (fun m acc => Bool.rec (motive := fun _ => Nat) acc (mulF2 28 acc (nthV G m))
      (CFSG.KLie.CT.bit j m)) 10

@[expose] noncomputable def selK (b : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) GQ2 GQ1 (Nat.beq b 1)

@[expose] noncomputable def okB (b : Nat) : Bool := orB (Nat.beq b 1) (Nat.beq b 2)

@[expose] noncomputable def letterK (h : Nat) (l : Nat × (Nat × Nat)) : Bool :=
  andB (okB l.1) (strictB (pcK (selK l.1) l.2.1) fun pj =>
    Nat.beq (mulF2 28 (mulF2 28 pj (pcK (selK l.1) l.2.2)) h) (mulF2 28 h pj))

@[expose] noncomputable def lettersK (h : Nat) (w : List (Nat × (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => andB (letterK h l) ih) w

@[expose] noncomputable def wordK (w : List (Nat × (Nat × Nat))) : Nat :=
  List.rec (motive := fun _ => Nat) (oneF2 28) (fun l _ ih => mulF2 28 (pcK (selK l.1) l.2.2) ih) w

@[expose] noncomputable def itemK (h : Nat) (d : Nat × List (List (Nat × (Nat × Nat)))) : Bool :=
  andB (okB d.1) (allN 10 fun m => andB (lettersK h (d.2.getD m []))
    (Nat.beq (wordK (d.2.getD m [])) (nthV (selK d.1) m)))

@[expose] noncomputable def torusK (tc : List (Nat × List (List (Nat × (Nat × Nat)))))
    (ht : List Nat) : Bool :=
  allN 9 fun s => strictB (sortedAt 28 12 6 2 EH.CF s) fun X =>
    bIf(Nat.beq X (oneF2 28), true, itemK X (tc.getD (nthV ht s) (0, [])))

@[expose] noncomputable def repK (ws : List (List Nat)) (i : Nat) : Nat := wordF4 gK (nthL ws i)

@[expose] noncomputable def cellK (rw : List (List Nat)) (i k : Nat) (e : Nat × Nat) : Bool :=
  andB (Nat.blt e.1 36) (andB (Nat.blt e.2 1024)
    (Nat.beq (mulF2 28 (repK rw i) (nthV gK k)) (mulF2 28 (sortedAt 28 12 6 10 EQ2.CF e.2) (repK rw e.1))))

@[expose] noncomputable def cosetK (rw rv : List (List Nat)) (rt rc : List (Nat × Nat)) : Bool :=
  andB (Nat.beq (repK rw 0) (oneF2 28)) <|
  andB (Nat.beq (repK rw 1) (blowW k2)) <|
  andB (Nat.beq (repK rw 2) (mulF2 28 (blowW k2) (blowW k2))) <|
  andB (allN 36 fun i => andB (Nat.beq (mulF2 28 (repK rw i) (repK rv i)) (oneF2 28))
    (allN 4 fun k => cellK rw i k (rt.getD (Nat.add (Nat.mul 4 i) k) (0, 0))))
  (allN 36 fun i => bIf(Nat.blt i 3, true, strictB (Prod.fst (rc.getD i (0, 0))) fun k =>
    andB (Nat.blt k 4) (gapK 28 12 6 10 EQ2.CF 1024 (Prod.snd (rc.getD i (0, 0)))
      (mulF2 28 (mulF2 28 (mulF2 28 (repK rw i) (nthV gK k)) (repK rv i)) (nthV (gMiK 0) k)))))

@[expose] noncomputable def kPowK (e : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (mulF2 28 (blowW k2) (blowW k2)) (blowW k2) (Nat.beq e 0)

@[expose] noncomputable def ord3StepK (idx j : Nat) : Bool :=
  strictB (mulF2 28 (sortedAt 28 12 6 10 EQ2.CF (Nat.mod idx 1024)) (kPowK (Nat.div idx 1024))) fun Y =>
    bIf(Nat.beq (mulF2 28 (mulF2 28 Y Y) Y) (oneF2 28),
      andB (Nat.blt j 1024) (strictB (pcK GQ2 j) fun T => strictB (mulF2 28 Y T) fun YT =>
        orB (Nat.beq YT (mulF2 28 T (blowW k2)))
          (Nat.beq YT (mulF2 28 T (mulF2 28 (blowW k2) (blowW k2))))), true)

@[expose] noncomputable def ord3GoK (o3 : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun j _ ih idx => andB (ord3StepK idx j) (ih (Nat.succ idx))) o3

@[expose] noncomputable def ord3QK (o3 : List Nat) : Bool :=
  andB (Nat.beq (List.length o3) 2048) (ord3GoK o3 0)

@[expose] noncomputable def centK : Bool :=
  andB (Nat.beq (mulF2 28 (mulF2 28 (blowW k2) (blowW k2)) (blowW k2)) (oneF2 28)) <|
  andB (allN 4 fun m => commK (blowW k2) (nthV GQ2 (Nat.add m 6)))
    (allN 1024 fun j => strictB (pcK GQ2 j) fun T =>
      bIf(commK T (blowW k2), Nat.beq (Nat.mod j 64) 0, true))

@[expose] noncomputable def eK (ej : List Nat) : Bool :=
  andB (commK (blowW k2) (bX 1)) <| andB (commK (blowW k2) (bX 2))
    (allN 4 fun s => strictB (sortedAt 28 12 6 2 EE.CF s) fun X =>
      bIf(Nat.beq X (oneF2 28), true, gapK 28 12 6 10 EQ2.CF 1024 (nthV ej s) X))

theorem ch733011_torus : torusK tc ht = true := by quickRfl
theorem ch733011_cosets : cosetK rw rv rt rc = true := by quickRfl
theorem ch733011_order3 : ord3QK o3 = true := by quickRfl
theorem ch733011_cent : centK = true := by quickRfl
theorem ch733011_eHead : headK 28 12 6 2 EE.CF = true := by quickRfl
theorem ch733011_ePins : allN 2 (fun j => Nat.beq (genR 28 12 6 2 EE.CF j) (nthV GE j)) = true := by
  quickRfl
theorem ch733011_eRecs : ∀ t < 4, recK2 28 12 6 2 EE.CF (genR 28 12 6 2 EE.CF) 4 t = true := by
  kc_cover 64
theorem ch733011_e : eK ej = true := by quickRfl

theorem ch733011_negTorus : (!torusK tc (ht.map Nat.succ)) = true := by quickRfl

theorem ch733011_negCosets : (!cosetK rv rw rt rc) = true := by quickRfl

theorem ch733011_negOrder3 : (!ord3QK (o3.map Nat.succ)) = true := by quickRfl

end CFSG.KD.G24B

end
