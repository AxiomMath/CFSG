module

public import Certificates.Data.Kernel.HD4Q2K
public import Certificates.Kernel.D4Plane.Checks
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json CFSG.KD.HD4Q2 "Certificates/Kernel/HuppertD4Q2/data/hd4q2.json" 96268
  9090308713242222626
  (recs : List CFSG.KC.HD4Q2K.Rec) (prs : List (List (Nat × Nat))) (r1 : List (Nat × Nat))
  (r2 : List (Nat × Nat)) (cg : List (List (Nat × Nat))) (ci : List (List (Nat × Nat)))

namespace CFSG.KD.HD4Q2

open CFSG.KC.HD4Q2K CFSG.KD.D4Plane CFSG.KC.D4PlaneP CFSG.KC.HTD42Q

@[expose] noncomputable def es : List (Nat × Nat) := recs.map fun m => m.2.1

theorem enumOK : enumQ ls es = true := by decide +kernel

theorem sylowOK : sylowQ ls es = true := by decide +kernel

theorem prsOK : prsQ es prs = true := by decide +kernel

theorem rowsOK : rowsQ ls es prs r1 r2 = true := by decide +kernel

theorem recsOK : recsQ es prs recs = true := by decide +kernel

@[expose] noncomputable def laneHW (s Y o : Nat) : Nat :=
  Nat.land s (Nat.mul (Nat.land (Nat.shiftRight Y o) (nat_lit 255)) r3)

@[expose] noncomputable def mulKHW (X Y k : Nat) : Nat :=
  (fun s o => Nat.xor (Nat.xor (laneHW s Y o) (Nat.shiftLeft (laneHW s Y (Nat.add (nat_lit 64) o))
    (nat_lit 64))) (Nat.shiftLeft (laneHW s Y (Nat.add (nat_lit 128) o)) (nat_lit 128)))
    (Nat.mul (Nat.land (Nat.shiftRight X k) r3) (nat_lit 255)) (Nat.mul (nat_lit 8) k)

@[expose] noncomputable def redHW (x : Nat) : Nat :=
  (fun a b => Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.land x m192) a) (Nat.shiftLeft a (nat_lit 64)))
    (Nat.shiftLeft b (nat_lit 64))) (Nat.shiftLeft b (nat_lit 128)))
    (Nat.land (Nat.shiftRight x (nat_lit 192)) m64) (Nat.shiftRight x (nat_lit 256))

@[expose] noncomputable def mulPW (X Y : Nat) : Nat :=
  redHW (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (mulKHW X Y (nat_lit 0))
    (mulKHW X Y (nat_lit 1))) (mulKHW X Y (nat_lit 2))) (mulKHW X Y (nat_lit 3)))
    (mulKHW X Y (nat_lit 4))) (mulKHW X Y (nat_lit 5))) (mulKHW X Y (nat_lit 6)))
    (mulKHW X Y (nat_lit 7)))

@[expose] noncomputable def frHW (X : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land X m64) (Nat.shiftLeft (Nat.land (Nat.shiftRight X (nat_lit 128)) m64)
    (nat_lit 64))) (Nat.shiftLeft (Nat.land (Nat.xor (Nat.shiftRight X (nat_lit 64))
      (Nat.shiftRight X (nat_lit 128))) m64) (nat_lit 128))

@[expose] noncomputable def frNW (n X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X (fun _ Y => frHW Y) n

@[expose] noncomputable def mulQW (p q : Nat × Nat) : Nat × Nat :=
  (mulPW p.1 (frNW p.2 q.1), Nat.mod (Nat.add p.2 q.2) (nat_lit 3))

@[expose] noncomputable def pairQW (m n : Rec) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Bool.rec (motive := fun _ => Bool) true
      ((Nat.beq m.2.2.2.1 n.1 && Nat.beq n.2.2.2.1 m.1) || shareQ m.2.2.2.2 n.2.2.2.2)
      (eqQ (mulQW m.2.1 n.2.1) (mulQW n.2.1 m.2.1)))
    n.2.2.1

@[expose] noncomputable def coverQW (recs : List Rec) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun m rest r => Bool.rec (motive := fun _ => Bool) false r
      (Bool.rec (motive := fun _ => Bool) true
        (List.rec (motive := fun _ => Bool) true
          (fun n _ s => Bool.rec (motive := fun _ => Bool) false s (pairQW m n)) rest)
        m.2.2.1)) recs

theorem coverQW_eq (L : List Rec) : coverQW L = coverQ L := rfl

theorem coverOK : coverQ recs = true := by
  rw [← coverQW_eq]
  decide +kernel

theorem classOK : (List.range 6).all (classQ ls cg ci) = true := by decide +kernel

theorem centerOK : centerQ ls es = true := by decide +kernel

theorem enumNeg : enumQ ls (es.set 5 oneQ) = false := by decide +kernel

theorem sylowNeg : sylowQ ls (es.set 5 (atQ es 6)) = false := by decide +kernel

theorem prsNeg : prsQ es (prs.set 0 (prs.getD 1 [])) = false := by decide +kernel

theorem rowsNeg : rowsQ ls es (prs.set 2 (prs.getD 3 [])) r1 r2 = false := by decide +kernel

theorem recsNeg : recsQ es (prs.set 0 []) recs = false := by decide +kernel

theorem coverNeg : coverQ (recs.map fun m => (m.1, m.2.1, m.2.2.1, m.2.2.2.1, [])) = false := by
  decide +kernel

theorem classNeg : classQ ls cg (ci.set 0 (cg.getD 0 [])) 0 = false := by decide +kernel

theorem centerNeg : centerQ ls (es.drop 1) = false := by decide +kernel

end CFSG.KD.HD4Q2
