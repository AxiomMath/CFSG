module

public import Certificates.Kernel.MonsterExist.Eb.Data
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.TwoA.Census.CosetEnumCheckInputs
public import CFSG.Monster.Existence.ELevelConv
public import Certificates.Kernel.MonsterExist.ShortKey.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.Eb

open CFSG.KC CFSG.KC.Loop CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster CFSG.Monster.B
  CFSG.Monster.Existence CFSG.Monster.B.TwoA.Census CertificateChecks.MonsterExist.ShortKey

@[expose] noncomputable def bXK (x y : Nat) : Nat :=
  Nat.xor (pairT x (Nat.shiftRight y (nat_lit 12))) (pairT y (Nat.shiftRight x (nat_lit 12)))

@[expose] noncomputable def case1V (v : Nat) : Bool :=
  bIf(Nat.beq (bXK v 782336) 1, true,
    bIf(Nat.beq (bXK v 520192) 1, true,
      bIf(memK (v ^^^ 782336),
        bIf(memK (v ^^^ 520192),
          bIf(memK (v ^^^ 782336 ^^^ 520192), false, true), true), true)))

@[expose] noncomputable def case1Bucket (a : Nat) : Bool :=
  (fun e => (fun vs => Nat.rec (motive := fun _ => Bool) true
      (fun k ih => bAnd(case1V (Nat.add a (Nat.mul (nat_lit 4096) (laneW (nat_lit 13) vs k))), ih)) (cntB e))
    (slice SKV (offB e) (cntB e))) (bkt a)

@[expose] noncomputable def case1Range (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(case1Bucket (Nat.add lo k), ih)) n

@[expose] noncomputable def allN (P : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(P k, ih)) n

@[expose] def actK (k n : Nat) : Nat := Rep4371.Native.CosetEnum.act (imgs 1) k n

@[expose] noncomputable def pt (i : Nat) : Nat := laneW (nat_lit 26) CL i

@[expose] noncomputable def spt (j : Nat) : Nat := laneW (nat_lit 26) SH j

@[expose] noncomputable def treeAt (i : Nat) : Bool :=
  (fun pl => (fun par lab => bAnd(Nat.blt par i, bAnd(Nat.blt lab (nat_lit 24),
      Nat.beq (pt i) (actK lab (pt par))))) (Nat.land pl (nat_lit 255)) (Nat.shiftRight pl (nat_lit 8)))
    (laneW (nat_lit 16) CP i)

@[expose] noncomputable def treeOK : Bool :=
  bAnd(Nat.beq (pt (nat_lit 0)) (classEnc 0), allN (fun i => treeAt (Nat.succ i)) (nat_lit 255))

@[expose] noncomputable def edgeAt (i k : Nat) : Bool :=
  (fun e => bAnd(Nat.blt e (nat_lit 256), Nat.beq (pt e) (actK k (pt i))))
    (laneW (nat_lit 8) CE (Nat.add (Nat.mul (nat_lit 24) i) k))

@[expose] noncomputable def edgeRange (lo n : Nat) : Bool :=
  allN (fun i => allN (fun k => edgeAt (Nat.add lo i) k) (nat_lit 24)) n

@[expose] noncomputable def boundOK : Bool :=
  bAnd(Nat.blt CL (Nat.shiftLeft (nat_lit 1) (nat_lit 6656)), bAnd(Nat.blt SH (Nat.shiftLeft (nat_lit 1) (nat_lit 3120)),
    bAnd(allN (fun i => Nat.blt (pt i) (nat_lit 33554432)) (nat_lit 256),
      allN (fun j => Nat.blt (spt j) (nat_lit 33554432)) (nat_lit 120))))

end CertificateChecks.MonsterExist.Eb

end
