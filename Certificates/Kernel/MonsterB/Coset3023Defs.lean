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

@[expose] noncomputable def c3PB : Nat := 326750844750520468301313714626966155427840

@[expose] noncomputable def c3ThStep (a : Nat) : Bool :=
  (fun n => (fun a' => andB (Nat.blt n 12) (andB (Nat.ble (pw2 n) a) (andB (Nat.blt a' (pw2 n))
      (Nat.beq (thetaL a) (Nat.xor (Nat.xor (thetaL a') (fget c3PB n 12))
        (dualT (Nat.land (wordT a') (bmT n)))))))) (Nat.sub a (pw2 n))) (thN a)

@[expose] noncomputable def c3ThOK : Bool :=
  andB (Nat.beq (thetaL 0) 0) (andB (Nat.blt (recT TH 6 16 0) (pw2 16))
    (allN 4095 fun j => c3ThStep (Nat.succ j)))

@[expose] noncomputable def thOK : Bool :=
  andB (Nat.beq (thetaL 0) 0) (andB (Nat.blt (recT TH 6 16 0) (pw2 16))
    (allN 4095 fun j => thStep (Nat.succ j)))

@[expose] noncomputable def tabE (TT : Nat → Nat) (j : Nat) : Model.Pauli := decW (recT TT 6 25 j)

@[expose] noncomputable def c3TabL (TT : Nat → Nat) (o : Nat) : Bool :=
  andB (decide (tabE TT o = (false, 0, 0)))
    (allN 12 fun n => allN (pw2 n) fun a => decide (tabE TT (Nat.add o (Nat.add (pw2 n) a)) =
      mulW (tabE TT (Nat.add o a)) (tabE TT (Nat.add o (pw2 n)))))

@[expose] noncomputable def c3TabBA (TT : Nat → Nat) (e : Nat) (pe : Bool) (P BT : Nat) : Bool :=
  allN 12 fun n => decide (alphaW e pe P BT (false, pw2 n, 0) = tabE TT (pw2 n))

@[expose] noncomputable def c3TabBD (TT : Nat → Nat) (e : Nat) (pe : Bool) (P BT : Nat) : Bool :=
  allN 12 fun n => decide (alphaW e pe P BT (false, 0, pw2 n) = tabE TT (Nat.add 4096 (pw2 n)))

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

@[expose] noncomputable def c3HW (TT : Nat → Nat) (w : Model.Pauli) (a d : Nat) : Nat :=
  Nat.mul 2 (oneW (prodW TT w false a d)).toNat

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

@[expose] noncomputable def c3BlockF (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (a : Nat) :
    Bool :=
  (fun k lo n => andB (Nat.ble (Nat.add lo n) 4096)
    (andB (bIf(Nat.beq n 0, true, andB (Nat.beq (kD TT (jpi J lo)) k)
        (Nat.beq (kD TT (jpi J (Nat.sub (Nat.add lo n) 1))) k)))
      (andB (bIf(Nat.beq lo 0, true, Nat.blt (kD TT (jpi J (Nat.sub lo 1))) k))
        (bIf(Nat.beq (Nat.add lo n) 4096, true, Nat.blt k (kD TT (jpi J (Nat.add lo n))))))))
    (kA TT w a) (jlo J a) (jn J a)

@[expose] noncomputable def c3BlocksF (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat)
    (lo m : Nat) : Bool :=
  allN m fun i => c3BlockF TT w J (Nat.add lo i)

@[expose] noncomputable def blockSum (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (a : Nat) :
    Nat :=
  sumN (jn J a) fun j => hW TT w a (jpi J (Nat.add (jlo J a) j))

@[expose] noncomputable def partOK (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (k v : Nat) :
    Bool :=
  Nat.beq (sumN 512 fun i => blockSum TT w J (Nat.add (Nat.mul 512 k) i)) v

@[expose] noncomputable def c3BlockSum (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (a : Nat) :
    Nat :=
  sumN (jn J a) fun j => c3HW TT w a (jpi J (Nat.add (jlo J a) j))

@[expose] noncomputable def c3PartK (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (k v : Nat) :
    Bool :=
  Nat.beq (sumN 512 fun i => c3BlockSum TT w J (Nat.add (Nat.mul 512 k) i)) v

@[expose] noncomputable def c3SgnA (w t : Model.Pauli) : Bool :=
  w.1 ^^ t.1 ^^ tb (pairT w.2.1 w.2.2) ^^ tb (pairT (Nat.xor w.2.1 t.2.1) t.2.2)

@[expose] noncomputable def c3HS (c : Bool) (u : Model.Pauli) (a : Nat) : Nat :=
  Nat.mul 2 (notB (c ^^ u.1 ^^ tb (pairT a u.2.2))).toNat

@[expose] noncomputable def c3BlockS (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (a : Nat) :
    Nat :=
  (fun c => sumN (jn J a) fun j => c3HS c (tabE TT (Nat.add 4096 (jpi J (Nat.add (jlo J a) j)))) a)
    (c3SgnA w (tabE TT a))

@[expose] noncomputable def c3PartS (TT : Nat → Nat) (w : Model.Pauli) (J : Nat → Nat) (k v : Nat) :
    Bool :=
  Nat.beq (sumN 512 fun i => c3BlockS TT w J (Nat.add (Nat.mul 512 k) i)) v

@[expose] noncomputable def sqW(TT : Nat → Nat) (w : Model.Pauli) (n : Nat) : Bool :=
  (fun s a d => andB (Nat.beq (kA TT w a) (kD TT d)) (oneW (prodW TT w s a d)))
    (tb (Nat.land (Nat.shiftRight n 24) 1)) (Nat.land n 4095)
    (Nat.land (Nat.shiftRight n 12) 4095)

@[expose] def actA (k n : Nat) : Nat := Rep4371.Native.CosetEnum.act imgs1L k n

@[expose] def actB (k n : Nat) : Nat := Rep4371.Native.CosetEnum.act imgs2L k n

@[expose] noncomputable def c3Img1 : Nat :=
  1037378907678398562041525057714733863414500542597812713616536987277876623556090117986226599675049913042280317488450281485805794256100641074505868618001647418805460088214628390387713

@[expose] noncomputable def c3Img2 : Nat :=
  1037378907678400404803535018651020618702443081211355944244613210284776183086523841938192649832565060771315311493072293672771780872811625839820252184383656613213077814420330123223102

@[expose] noncomputable def c3EncW (x : Model.Pauli) : Nat :=
  Nat.add (Nat.land x.2.1 4095) (Nat.add (Nat.mul 4096 (Nat.land x.2.2 4095))
    (Bool.rec 0 16777216 x.1))

@[expose] noncomputable def c3InvW (x : Model.Pauli) : Model.Pauli :=
  (x.1 ^^ tb (pairT x.2.1 x.2.2), x.2.1, x.2.2)

@[expose] noncomputable def c3GenPW (k : Nat) : Model.Pauli :=
  Bool.rec (false, 0, pw2 (Nat.sub k 12)) (false, pw2 k, 0) (Nat.blt k 12)

@[expose] noncomputable def c3ImgW (I k : Nat) : Model.Pauli :=
  decW (Nat.land (Nat.shiftRight I (Nat.mul 25 k)) 33554431)

@[expose] noncomputable def c3ActK (I k n : Nat) : Nat :=
  c3EncW (mulW (c3InvW (c3ImgW I k)) (mulW (decW n) (c3GenPW k)))

@[expose] noncomputable def rec1 (k i : Nat) : Nat := recT CL1 6 44 (Nat.add (Nat.mul 512 k) i)

@[expose] noncomputable def rec2 (i : Nat) : Nat := recT CL2 6 47 i

@[expose] noncomputable def tree1 (k : Nat) : Bool :=
  andB (Nat.beq (valF 25 (rec1 k 0)) (classEnc k))
    (treeOK actA 24 (fun _ => true) (classEnc k) (rec1 k) (classSize k) 25 4 9 64 8)

@[expose] noncomputable def trees1 (lo n : Nat) : Bool := allN n fun j => tree1 (Nat.add lo j)

@[expose] noncomputable def c3Tree1K (k : Nat) : Bool :=
  andB (Nat.beq (valF 25 (rec1 k 0)) (classEnc k))
    (treeOK (c3ActK c3Img1) 24 (fun _ => true) (classEnc k) (rec1 k) (classSize k) 25 4 9 64 8)

@[expose] noncomputable def c3Trees1K (lo n : Nat) : Bool := allN n fun j => c3Tree1K (Nat.add lo j)

@[expose] noncomputable def c3Tree2K : Bool :=
  andB (Nat.beq (valF 25 (rec2 0)) 734)
    (treeOK (c3ActK c3Img2) 24 (fun _ => true) 734 rec2 8192 25 4 13 64 128)

@[expose] noncomputable def c3EdgesK (m : Nat) : Bool :=
  closeOK (c3ActK c3Img1) 24 (rec1 (Nat.mul 4 m)) (fun i k => recT ED 6 8 (Nat.add (Nat.mul 6144 m)
    (Nat.add (Nat.mul 24 i) k))) 256 25 64 4

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
