module

public import Certificates.Kernel.MonsterB.Coset3023Data
public import CFSG.Monster.B.TwoA.Census.CosetEnumCheckInputs

public section

namespace CertificateChecks.Coset3023

open CFSG.KC.KDense CFSG.KLie.CT CFSG.Monster.B CFSG.KC.SortTree CFSG.KC.U6Orb
  CFSG.Monster.B.TwoA.Census

@[expose] noncomputable def thN (a : Nat) : Nat := Nat.shiftRight (recT TH 6 16 a) 12

@[expose] noncomputable def thStep (a : Nat) : Bool :=
  (fun n => (fun a' => andB (Nat.blt n 12) (andB (Nat.ble (pw2 n) a) (andB (Nat.blt a' (pw2 n))
      (Nat.beq (thetaL a) (Nat.xor (Nat.xor (thetaL a') (packBetaT n))
        (dualT (Nat.land (wordT a') (bmT n)))))))) (Nat.sub a (pw2 n))) (thN a)

@[expose] noncomputable def thOK : Bool :=
  andB (Nat.beq (thetaL 0) 0) (andB (Nat.blt (recT TH 6 16 0) (pw2 16))
    (allN 4095 fun j => thStep (Nat.succ j)))

@[expose] noncomputable def tabE (TT : Nat → Nat) (j : Nat) : Model.Pauli := decW (recT TT 6 25 j)

@[expose] noncomputable def tabA (TT : Nat → Nat) (e : Nat) (pe : Bool) (P BT : Nat) : Bool :=
  allN 4096 fun A => decide (alphaW e pe P BT (false, A, 0) = tabE TT A)

@[expose] noncomputable def tabD (TT : Nat → Nat) (e : Nat) (pe : Bool) (P BT : Nat) : Bool :=
  allN 4096 fun D => decide (alphaW e pe P BT (false, 0, D) = tabE TT (Nat.add 4096 D))

@[expose] noncomputable def kA (TT : Nat → Nat) (w : Model.Pauli) (a : Nat) : Nat :=
  (fun t : Model.Pauli => Nat.add (Nat.land (Nat.xor (Nat.xor a w.2.1) t.2.1) 4095)
    (Nat.mul 4096 (Nat.land (Nat.xor w.2.2 t.2.2) 4095))) (tabE TT a)

@[expose] noncomputable def kD (TT : Nat → Nat) (d : Nat) : Nat :=
  (fun u : Model.Pauli => Nat.add (Nat.land u.2.1 4095)
    (Nat.mul 4096 (Nat.land (Nat.xor d u.2.2) 4095))) (tabE TT (Nat.add 4096 d))

@[expose] noncomputable def oneW (x : Model.Pauli) : Bool :=
  andB (notB x.1) (andB (Nat.beq (Nat.land x.2.1 4095) 0) (Nat.beq (Nat.land x.2.2 4095) 0))

@[expose] noncomputable def prodW (TT : Nat → Nat) (w : Model.Pauli) (s : Bool) (a d : Nat) :
    Model.Pauli :=
  mulW (s, a, d) (mulW w (mulW (s, 0, 0) (mulW (tabE TT a) (tabE TT (Nat.add 4096 d)))))

@[expose] noncomputable def hW (TT : Nat → Nat) (w : Model.Pauli) (a d : Nat) : Nat :=
  Nat.add (oneW (prodW TT w false a d)).toNat (oneW (prodW TT w true a d)).toNat

@[expose] noncomputable def jF (J : Nat → Nat) (j o w : Nat) : Nat :=
  Nat.land (Nat.shiftRight (recT J 6 50 j) o) (maskN w)

@[expose] noncomputable def jpi (J : Nat → Nat) (j : Nat) : Nat := jF J j 0 12

@[expose] noncomputable def jrho (J : Nat → Nat) (d : Nat) : Nat := jF J d 12 12

@[expose] noncomputable def jlo (J : Nat → Nat) (a : Nat) : Nat := jF J a 24 13

@[expose] noncomputable def jn (J : Nat → Nat) (a : Nat) : Nat := jF J a 37 13

@[expose] noncomputable def blockOK (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (a : Nat) :
    Bool :=
  (fun k lo n => andB (Nat.ble (Nat.add lo n) 4096)
    (andB (allN n fun j => Nat.beq (kD TT (jpi J (Nat.add lo j))) k)
      (andB (bIf(Nat.beq lo 0, true, Nat.blt (kD TT (jpi J (Nat.sub lo 1))) k))
        (bIf(Nat.beq (Nat.add lo n) 4096, true, Nat.blt k (kD TT (jpi J (Nat.add lo n))))))))
    (kA TT w a) (jlo J a) (jn J a)

@[expose] noncomputable def sortOK (TT : Nat → Nat) (J : Nat → Nat) : Bool :=
  andB (allN 4096 fun d => andB (Nat.beq (jpi J (jrho J d)) d) (Nat.beq (jrho J (jpi J d)) d))
    (allN 4095 fun j => Nat.ble (kD TT (jpi J j)) (kD TT (jpi J (Nat.succ j))))

@[expose] noncomputable def blocksOK (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (lo m : Nat) :
    Bool :=
  allN m fun i => blockOK TT w J (Nat.add lo i)

@[expose] noncomputable def blockSum (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (a : Nat) :
    Nat :=
  sumN (jn J a) fun j => hW TT w a (jpi J (Nat.add (jlo J a) j))

@[expose] noncomputable def partOK (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (k v : Nat) :
    Bool :=
  Nat.beq (sumN 512 fun i => blockSum TT w J (Nat.add (Nat.mul 512 k) i)) v

@[expose] noncomputable def sqW (TT : Nat → Nat) (w : Model.Pauli) (n : Nat) : Bool :=
  (fun s a d => andB (Nat.beq (kA TT w a) (kD TT d)) (oneW (prodW TT w s a d)))
    (tb (Nat.land (Nat.shiftRight n 24) 1)) (Nat.land n 4095)
    (Nat.land (Nat.shiftRight n 12) 4095)

@[expose] def actA (k n : Nat) : Nat := Rep4371.Native.CosetEnum.act imgs1L k n

@[expose] def actB (k n : Nat) : Nat := Rep4371.Native.CosetEnum.act imgs2L k n

@[expose] noncomputable def rec1 (k i : Nat) : Nat := recT CL1 6 44 (Nat.add (Nat.mul 512 k) i)

@[expose] noncomputable def rec2 (i : Nat) : Nat := recT CL2 6 47 i

@[expose] noncomputable def tree1 (k : Nat) : Bool :=
  andB (Nat.beq (valF 25 (rec1 k 0)) (classEnc k))
    (treeOK actA 24 (fun _ => true) (classEnc k) (rec1 k) (classSize k) 25 4 9 64 8)

@[expose] noncomputable def trees1 (lo n : Nat) : Bool := allN n fun j => tree1 (Nat.add lo j)

@[expose] noncomputable def tree2 : Bool :=
  andB (Nat.beq (valF 25 (rec2 0)) 734) (treeOK actB 24 (fun _ => true) 734 rec2 8192 25 4 13 64 128)

@[expose] noncomputable def edges (m : Nat) : Bool :=
  closeOK actA 24 (rec1 (Nat.mul 4 m)) (fun i k => recT ED 6 8 (Nat.add (Nat.mul 6144 m)
    (Nat.add (Nat.mul 24 i) k))) 256 25 64 4

@[expose] noncomputable def comb (B n m : Nat) : Nat :=
  xorK n fun j => nIf(bit m j, fget B j (nat_lit 24), nat_lit 0)

@[expose] noncomputable def spanOK (act : Nat → Nat → Nat) (B C n : Nat) : Bool :=
  allN 24 fun k => andB (Nat.blt (fget C k 12) (pw2 n))
    (Nat.beq (comb B n (fget C k 12)) (Nat.land (act k 0) (nat_lit 16777215)))

end CertificateChecks.Coset3023

end
