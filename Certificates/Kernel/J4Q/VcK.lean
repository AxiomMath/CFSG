module

public import Certificates.Kernel.J4Q.VlBase
public import Certificates.Kernel.J4Q.X0Orb
public import Certificates.Kernel.J4Q.VcData
public import CFSG.Sporadic.J4.QT2LocVLClassNative
import Certificates.Kernel.J4Q.Strs

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.VA9 CFSG.Sporadic.J4.QT2.vlA941Strs
#j4q_strs CFSG.KD.J4Q.VB7 CFSG.QuasithinUnique.A5.B7.b7ExplicitWords
#j4q_strs CFSG.KD.J4Q.VBS CFSG.Sporadic.J4.QT2.vlB336Word

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q

@[expose] noncomputable def sameK (A B : List Nat) : Bool :=
  andB (allLK (fun x => inLK x B) A) (allLK (fun x => inLK x A) B)

@[expose] noncomputable def gaK (g : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) (grpK (Nat.sub g 17))
    (smapK (fun j => CFSG.KD.ETA.EF (getN 0 IL17 (Nat.add (Nat.mul 16 g) j))) (rangeK 16))
    (Nat.blt g 17)

@[expose] noncomputable def conjLK (x xi : Nat) (A : List Nat) : List Nat :=
  smapK (fun M => mulJ c rm (mulJ c rm x M) xi) A

@[expose] noncomputable def vcK (g : Nat) : Bool :=
  (fun r cc ci => andB (inLK r VREP) (andB (Nat.blt r 149) (andB (Nat.blt cc 6720)
    (andB (Nat.blt ci 6720)
      ((fun x xi => andB (canonJ pad xi) (andB (Nat.beq (mulJ c rm x xi) one)
        (sameK (conjLK x xi (gaK r)) (gaK g)))) (CFSG.KD.X0O.MSF cc) (CFSG.KD.X0O.MSF ci))))))
    (getN 0 VCR g) (getN 0 VCC g) (getN 0 VCI g)

@[expose] noncomputable def ngK (k i : Nat) : Nat := getN one VNG (Nat.add (Nat.mul 4 k) i)

@[expose] noncomputable def nsK (k : Nat) : List Nat := d4SK (ngK k 0) (ngK k 1) (ngK k 2) (ngK k 3)

@[expose] noncomputable def closedK (A : List Nat) : Bool :=
  andB (inLK one A) (allLK (fun M => andB (Nat.beq (mulJ c rm M M) one)
    (allLK (fun N => inLK (mulJ c rm M N) A) A)) A)

@[expose] noncomputable def nmK (k : Nat) : Bool :=
  (fun r => (fun A S => andB (closedK A) (andB (Nat.beq (lenK A) 16)
    (andB (allR 4 fun i => inLK (ngK k i) A) (andB (allLK (fun s => inLK s A) S)
      (andB (distK S) (andB (Nat.blt r 149) (andB (sameK S (gaK r))
        (allR r fun g => notB (sameK S (gaK g)))))))))) (gaK r) (nsK k)) (getN 0 VREP k)

@[expose] noncomputable def vA9W : List (List Int) := [
  w5K (List.flatten [VA9.s0, VA9.s1, VA9.s2, VA9.s3]),
  w5K (List.flatten [VA9.s4, VA9.s5, VA9.s6, VA9.s7]),
  w5K (List.flatten [VA9.s8, VA9.s9, VA9.s10, VA9.s11, VA9.s12, VA9.s13]),
  w5K (List.flatten [VA9.s14, VA9.s15, VA9.s16])]

@[expose] noncomputable def vB7W : List (List Int) := [
  w5K (List.flatten [VB7.s0, VB7.s1, VB7.s2, VB7.s3, VB7.s4, VB7.s5]),
  w5K (List.flatten [VB7.s6, VB7.s7, VB7.s8, VB7.s9]),
  w5K (List.flatten [VB7.s10, VB7.s11, VB7.s12, VB7.s13, VB7.s14]),
  w5K (List.flatten [VB7.s15, VB7.s16, VB7.s17, VB7.s18, VB7.s19, VB7.s20, VB7.s21, VB7.s22])]

@[expose] noncomputable def vBSW : List Int := w5K VBS.s0

@[expose] noncomputable def ngMasks : List Nat :=
  [1056, 321, 43, 796, 768, 299, 213, 1414, 25, 136, 833, 1312]

@[expose] noncomputable def getW (l : List (List Int)) (i : Nat) : List Int :=
  List.rec (motive := fun _ => Nat → List Int) (fun _ => List.nil)
    (fun m _ ih i => Nat.rec (motive := fun _ => List Int) m (fun j _ => ih j) i) l i

@[expose] noncomputable def ngMaskOK : Bool :=
  allR 4 fun i => andB (Nat.beq (ngK 0 i) (CFSG.KD.ETA.EF (getN 0 ngMasks i)))
    (andB (Nat.beq (ngK 1 i) (CFSG.KD.ETA.EF (getN 0 ngMasks (Nat.add 4 i))))
      (Nat.beq (ngK 5 i) (CFSG.KD.ETA.EF (getN 0 ngMasks (Nat.add 8 i)))))

@[expose] noncomputable def ngA9OK (i : Nat) : Bool :=
  Nat.beq (ngK 2 i) (wordJ c rm one G5 G5i (getW vA9W i))

@[expose] noncomputable def ngB7OK (i : Nat) : Bool :=
  Nat.beq (ngK 3 i) (wordJ c rm one G5 G5i (getW vB7W i))

@[expose] noncomputable def ngB3OK : Bool := allR 4 fun i => Nat.beq (ngK 4 i) (getN one B3G i)

@[expose] noncomputable def ngXiMasks : List Nat := [37, 97, 236, 491]

@[expose] noncomputable def ngXiOK (j : Nat) : Bool :=
  (fun k => andB (Nat.beq (ngK k 0)
      (mulJ c rm (CFSG.KD.ETA.EF (getN 0 ngXiMasks j)) (wordJ c rm one G5 G5i vBSW)))
    (allR 3 fun i => Nat.beq (ngK k (Nat.succ i)) (cjV (ngK k i)))) (Nat.add 6 j)

end CertificateChecks.KernelJ4Q

end
