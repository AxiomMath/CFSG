module

public import Certificates.Kernel.HNFSub.Data
public import Certificates.Data.Kernel.HNFDfsK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.HNFSub

@[expose] noncomputable def joinL (L : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun l _ ih => CFSG.KC.HNFDfs.appN l ih) L

@[expose] noncomputable def fil (f : Nat → Bool) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun k _ ih => Bool.rec (motive := fun _ => List Nat) ih (k :: ih) (f k)) l

@[expose] noncomputable def cAt (i : Nat) : Nat := CFSG.KC.HNF26729.getN 0 O7.cs i

@[expose] noncomputable def bkt (j : Nat) (k : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (Nat.ble (cAt 2) k)
        (CFSG.KC.Ord.andB (Nat.ble (cAt 1) k) (Nat.blt k (cAt 2))) (Nat.beq j 2))
      (CFSG.KC.Ord.andB (Nat.ble (cAt 0) k) (Nat.blt k (cAt 1))) (Nat.beq j 1))
    (Nat.blt k (cAt 0)) (Nat.beq j 0)

@[expose] noncomputable def ordB (j : Nat) : List Nat :=
  joinL (Bool.rec (motive := fun _ => List (List Nat))
    (Bool.rec (motive := fun _ => List (List Nat))
      (Bool.rec (motive := fun _ => List (List Nat)) O7.o3 O7.o2 (Nat.beq j 2)) O7.o1 (Nat.beq j 1))
    O7.o0 (Nat.beq j 0))

theorem keys_len : (CFSG.KC.HNFSub.allKeys S7.segs).length = 88704 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem bkt_len0 : (fil (bkt 0) (CFSG.KC.HNFSub.allKeys S7.segs)).length = 22176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem ord_len0 : (ordB 0).length = 22176 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem dist0 : CFSG.KC.HNFDfs.distL (fil (bkt 0) (CFSG.KC.HNFSub.allKeys S7.segs)) (ordB 0) = true := by
  quickRfl

theorem bkt_len1 : (fil (bkt 1) (CFSG.KC.HNFSub.allKeys S7.segs)).length = 22176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem ord_len1 : (ordB 1).length = 22176 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem dist1 : CFSG.KC.HNFDfs.distL (fil (bkt 1) (CFSG.KC.HNFSub.allKeys S7.segs)) (ordB 1) = true := by
  quickRfl

theorem bkt_len2 : (fil (bkt 2) (CFSG.KC.HNFSub.allKeys S7.segs)).length = 22176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem ord_len2 : (ordB 2).length = 22176 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem dist2 : CFSG.KC.HNFDfs.distL (fil (bkt 2) (CFSG.KC.HNFSub.allKeys S7.segs)) (ordB 2) = true := by
  quickRfl

theorem bkt_len3 : (fil (bkt 3) (CFSG.KC.HNFSub.allKeys S7.segs)).length = 22176 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem ord_len3 : (ordB 3).length = 22176 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem dist3 : CFSG.KC.HNFDfs.distL (fil (bkt 3) (CFSG.KC.HNFSub.allKeys S7.segs)) (ordB 3) = true := by
  quickRfl

end CFSG.KD.HNFSub

end
