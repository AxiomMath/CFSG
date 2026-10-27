module

public import Certificates.Kernel.G24B.Checks733008
public import Certificates.Kernel.G24B.RecChecks
public import Certificates.Kernel.G24B.RecsZ
public import Certificates.Kernel.G24B.RData
public import Certificates.Data.G24IdentPc
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.KC.Misc.G24 CFSG.KC.F2BfsRec CFSG.KLie.CT CFSG.KC.M1F2

@[expose] noncomputable def r10StepK (EQ EZ : Nat → Nat) (GQ : List Nat) (ngz nZ s : Nat)
    (d : Nat × (Nat × Nat)) : Bool :=
  strictB (sortedAt 28 12 6 10 EQ s) fun X =>
    andB (orB (andB (Nat.blt d.1 10) (notB (commK X (nthV GQ d.1))))
        (andB (Nat.blt d.2.1 nZ) (Nat.beq X (sortedAt 28 12 6 ngz EZ d.2.1))))
      (andB (Nat.blt d.2.2 nZ) (Nat.beq (mulF2 28 X X) (sortedAt 28 12 6 ngz EZ d.2.2)))

@[expose] noncomputable def r10GoK (EQ EZ : Nat → Nat) (GQ : List Nat) (ngz nZ : Nat)
    (ws : List (Nat × (Nat × Nat))) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun d _ ih s => andB (r10StepK EQ EZ GQ ngz nZ s d) (ih (Nat.succ s))) ws

@[expose] noncomputable def r10K (EQ EZ : Nat → Nat) (GQ : List Nat) (k ngz nZ : Nat)
    (ws : List (Nat × (Nat × Nat))) (cm : List Nat) : Bool :=
  andB (Nat.beq (List.length ws) 1024) <|
  andB (allN ngz fun t => allN 10 fun m => commK (nthV GQ (Nat.add k t)) (nthV GQ m)) <|
  andB (allN nZ fun s => strictB (sortedAt 28 12 6 ngz EZ s) fun X =>
    Nat.beq (mulF2 28 X X) (oneF2 28)) <|
  andB (allN 10 fun m => allN 10 fun m' => strictB (nthV cm (Nat.add (Nat.mul 10 m) m')) fun c =>
    andB (Nat.blt c nZ) (Nat.beq (mulF2 28 (nthV GQ m) (nthV GQ m'))
      (mulF2 28 (sortedAt 28 12 6 ngz EZ c) (mulF2 28 (nthV GQ m') (nthV GQ m)))))
  (r10GoK EQ EZ GQ ngz nZ ws 0)

@[expose] noncomputable def r10PowK (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X (fun _ acc => mulF2 28 acc X) e

@[expose] noncomputable def r10InvK (G es : List Nat) (i : Nat) : Nat := r10PowK (nthV G i) (nthV es i)

@[expose] noncomputable def r10InvOK (G es : List Nat) (n : Nat) : Bool :=
  allN n fun i => Nat.beq (mulF2 28 (r10InvK G es i) (nthV G i)) (oneF2 28)

@[expose] noncomputable def r10SgK {m : Nat} (G Gi : Nat → Nat) (w : List (Fin m × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (oneF2 28)
    (fun l _ ih => mulF2 28 (Bool.rec (motive := fun _ => Nat) (Gi l.1.val) (G l.1.val) l.2) ih) w

@[expose] noncomputable def r10RelsK {m : Nat} (G Gi : Nat → Nat) (rels : List (List (Fin m × Bool))) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (Nat.beq (r10SgK G Gi r) (oneF2 28)) ih) rels

@[expose] noncomputable def r10ImgK (G Gi : Nat → Nat) (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Gi i) (G i) (Nat.beq i 0)

@[expose] def r10EQ : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

@[expose] def r10EA : List Nat := [0, 1, 1]

theorem ch733010_z1Head : headK 28 12 6 2 EZ1.CF = true := by quickRfl
theorem ch733010_z1Pins : pinsK 6 2 EZ1.CF wZ1 = true := by quickRfl
theorem ch733010_z1Recs : ∀ t < 4, recK2 28 12 6 2 EZ1.CF (genR 28 12 6 2 EZ1.CF) 4 t = true := by
  kc_cover 64

theorem ch733010_z2Head : headK 28 12 6 4 EZ2.CF = true := by quickRfl
theorem ch733010_z2Pins : pinsK 6 4 EZ2.CF wZ2 = true := by quickRfl
theorem ch733010_z2Recs : ∀ t < 16, recK2 28 12 6 4 EZ2.CF (genR 28 12 6 4 EZ2.CF) 16 t = true := by
  kc_cover 64

theorem ch733010_rad1 : r10K EQ1.CF EZ1.CF GQ1 8 2 4 w1 c1 = true := by quickRfl
theorem ch733010_rad2 : r10K EQ2.CF EZ2.CF GQ2 6 4 16 w2 c2 = true := by quickRfl

theorem ch733010_invQ1 : r10InvOK GQ1 r10EQ 10 = true := by quickRfl
theorem ch733010_invQ2 : r10InvOK GQ2 r10EQ 10 = true := by quickRfl
theorem ch733010_invA1 : r10InvOK GA1 r10EA 3 = true := by quickRfl
theorem ch733010_invA2 : r10InvOK GA2 r10EA 3 = true := by quickRfl

theorem ch733010_relsQ1 :
    r10RelsK (nthV GQ1) (r10InvK GQ1 r10EQ) CFSG.Quasithin.St84.G24Pc.relsQ1 = true := by quickRfl
theorem ch733010_relsQ2 :
    r10RelsK (nthV GQ2) (r10InvK GQ2 r10EQ) CFSG.Quasithin.St84.G24Pc.relsQ2 = true := by quickRfl
theorem ch733010_relsA1 :
    r10RelsK (nthV GA1) (r10InvK GA1 r10EA) CFSG.Quasithin.St84.G24Pc.relsA = true := by quickRfl
theorem ch733010_relsA2 :
    r10RelsK (nthV GA2) (r10InvK GA2 r10EA) CFSG.Quasithin.St84.G24Pc.relsA = true := by quickRfl
theorem ch733010_relsA1img :
    r10RelsK (r10ImgK (nthV GA1) (r10InvK GA1 r10EA)) (r10ImgK (r10InvK GA1 r10EA) (nthV GA1))
      CFSG.Quasithin.St84.G24Pc.relsA = true := by quickRfl
theorem ch733010_relsA2img :
    r10RelsK (r10ImgK (nthV GA2) (r10InvK GA2 r10EA)) (r10ImgK (r10InvK GA2 r10EA) (nthV GA2))
      CFSG.Quasithin.St84.G24Pc.relsA = true := by quickRfl

theorem ch733010_gap12 : gapK 28 12 6 10 EQ2.CF 1024 g12 (nthV GQ1 3) = true := by quickRfl

theorem ch733010_negRad : (!r10K EQ1.CF EZ1.CF GQ1 8 2 4 (w1.tail ++ w1.take 1) c1) = true := by
  quickRfl

theorem ch733010_negRels :
    (!r10RelsK (nthV GQ2) (r10InvK GQ2 r10EQ) CFSG.Quasithin.St84.G24Pc.relsQ1) = true := by
  quickRfl

theorem ch733010_negGap : (!gapK 28 12 6 10 EQ2.CF 1024 (g12 + 1) (nthV GQ1 3)) = true := by
  quickRfl

end CFSG.KD.G24B

end
