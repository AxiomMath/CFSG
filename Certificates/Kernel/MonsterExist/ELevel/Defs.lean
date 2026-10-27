module

public import Certificates.Kernel.MonsterExist.Eb.Defs
public import CFSG.Monster.Existence.ELevelCheck

public section

namespace CertificateChecks.MonsterExist.ELevel

open CFSG.KC CFSG.KC.Loop CFSG.KC.KDense CFSG.Monster CFSG.Monster.B CFSG.Monster.Existence
  CertificateChecks.MonsterExist.ShortKey CertificateChecks.MonsterExist.Eb

@[expose] noncomputable def xorFold (B x lo : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (selB (bitN x (Nat.add lo k)) (laneW (nat_lit 25) B k))) (nat_lit 12)

@[expose] noncomputable def kapL (TB DB x : Nat) : Nat :=
  Nat.land (Nat.xor (xorFold TB x (nat_lit 0)) (xorFold DB x (nat_lit 12))) (nat_lit 16777215)

@[expose] noncomputable def pmul (p q : Nat) : Nat :=
  Nat.xor (Nat.xor p q)
    (Nat.shiftLeft (pairT (Nat.land q (nat_lit 4095)) (Nat.land (Nat.shiftRight p (nat_lit 12)) (nat_lit 4095))) (nat_lit 24))

@[expose] noncomputable def pfold (B x lo : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => nIf(Nat.beq (bitN x (Nat.add lo k)) (nat_lit 1), pmul acc (laneW (nat_lit 25) B k), acc)) (nat_lit 12)

@[expose] noncomputable def csK (TB DB x : Nat) : Nat :=
  bitN (pmul (pfold TB x (nat_lit 0)) (pfold DB x (nat_lit 12))) (nat_lit 24)

@[expose] noncomputable def synL (FB : List Nat) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun f _ ih => Nat.add (bXK f y) (Nat.mul (nat_lit 2) ih)) FB

@[expose] noncomputable def tPoint (e : Nat) : Nat :=
  Nat.shiftLeft (Nat.land e (nat_lit 255)) (Nat.mul (nat_lit 8) (Nat.shiftRight e (nat_lit 8)))

@[expose] noncomputable def ttOK (TB DB : Nat) (FB : List Nat) (TT : Nat) : Bool :=
  allN (fun e => Nat.beq (laneW (nat_lit 40) TT e)
    (Nat.lor (kapL TB DB (tPoint e)) (Nat.shiftLeft (synL FB (tPoint e)) (nat_lit 24)))) (nat_lit 768)

@[expose] noncomputable def tabK (TT x : Nat) : Nat :=
  Nat.xor (Nat.xor (laneW (nat_lit 40) TT (Nat.land x (nat_lit 255)))
      (laneW (nat_lit 40) TT (Nat.add (nat_lit 256) (Nat.land (Nat.shiftRight x (nat_lit 8)) (nat_lit 255)))))
    (laneW (nat_lit 40) TT (Nat.add (nat_lit 512) (Nat.land (Nat.shiftRight x (nat_lit 16)) (nat_lit 255))))

@[expose] noncomputable def passT (TT sw nCV CV nCS CS x : Nat) : Bool :=
  (fun t => bAnd(bIf(Nat.beq (Nat.land t (nat_lit 16777215)) x, bIf(absentL (nat_lit 25) nCV CV x, false, true), true),
      bIf(Nat.beq (Nat.shiftRight t (nat_lit 24)) sw, bIf(absentL (nat_lit 25) nCS CS x, false, true), true)))
    (tabK TT x)

@[expose] noncomputable def bucketAll (P : Nat → Bool) (a : Nat) : Bool :=
  (fun e => (fun vs => allN (fun k => P (Nat.add a (Nat.mul (nat_lit 4096) (laneW (nat_lit 13) vs k)))) (cntB e))
    (slice SKV (offB e) (cntB e))) (bkt a)

@[expose] noncomputable def passRange (P : Nat → Bool) (lo n : Nat) : Bool :=
  allN (fun k => bucketAll P (Nat.add lo k)) n

@[expose] noncomputable def thirdK (TB DB xw v : Nat) (su : Option Nat) (c s : Nat) : Bool :=
  Option.rec (motive := fun _ => Bool) false
    (fun u => bAnd(Nat.beq (Nat.xor u (kapL TB DB u)) v, bIf(Nat.beq (bXK (Nat.xor s xw) u) c, false, true))) su

@[expose] noncomputable def innerP (TB DB xw v : Nat) (su : Option Nat) (c s : Nat) : Bool :=
  bIf(Nat.beq (bXK s v) (nat_lit 1), true, bIf(memK (Nat.xor s v), thirdK TB DB xw v su c s, true))

@[expose] noncomputable def innerV (TB DB : Nat) (PIV : List (Nat × Nat)) (xw nCS CS v : Nat) : Bool :=
  (fun su c => allN (fun r => innerP TB DB xw v su c (laneW (nat_lit 25) CS r)) nCS)
    (solveX PIV v) (csK TB DB v)

@[expose] noncomputable def innerRange (TB DB : Nat) (PIV : List (Nat × Nat)) (xw nCS CS CV lo n : Nat) : Bool :=
  allN (fun t => innerV TB DB PIV xw nCS CS (laneW (nat_lit 25) CV (Nat.add lo t))) n

@[expose] noncomputable def TB1 : Nat := nat_lit 0x4000001002200401200100820040420010000603e00302f00181b800c0ec07800403c001

@[expose] noncomputable def DB1 : Nat := nat_lit 0x4000001000000400000100000040000010000003800602c00301a00180e000c07c07803d03c

@[expose] noncomputable def TB2 : Nat := nat_lit 0xaec41fe0010023b0401a5210050485fac441fc03c040b6101055080400840ec2420040de03e

@[expose] noncomputable def DB2 : Nat := nat_lit 0x400000100000240007e10000084001fc1000fd1ca5c28d52de46696f2304b7918e5bc8c42e1

@[expose] noncomputable def TB6 : Nat := nat_lit 0xb5841fea0d0f3a431612d44646a9507869145148b03898582c002c1c05ea02c90b07a63a801

@[expose] noncomputable def DB6 : Nat := nat_lit 0x55f800150000010000104003f10000044000ffe34293e6a149e5f0bb77c8527108293887176

@[expose] def PIV1 : List (ℕ × ℕ) := [(2097152, 256), (1048576, 512), (524288, 64), (262144, 128),
  (245763, 131072), (12288, 139296), (63, 139264), (3, 131074)]

@[expose] def FB1 : List ℕ := [3, 36, 40, 48, 1024, 2048, 12288, 147456, 163840, 196608, 262144, 524288,
  1048576, 2097152, 4194304, 8388608]

@[expose] def PIV2 : List (ℕ × ℕ) := [(9196254, 2228224), (6127616, 2099200), (2433024, 1280),
  (1168094, 2229760), (807646, 2229248), (372736, 2097536), (176128, 464), (111326, 2229984),
  (37598, 132396), (21214, 2229952), (13022, 2229496), (63, 2097152)]

@[expose] def FB2 : List ℕ := [2097889, 2097886, 135168, 2236416, 2244608, 2260992, 2293760, 2359296,
  2621440, 1048576, 4194304, 8388608]

@[expose] def PIV6 : List (ℕ × ℕ) := [(13390153, 12713984), (4255744, 15769600), (2879488, 8388608),
  (1310720, 4194304), (545098, 7349248), (311296, 3309568), (258048, 10485760), (125580, 140800),
  (41285, 14689600), (28631, 4237056), (14296, 14819936), (63, 5242880)]

@[expose] def FB6 : List ℕ := [4334625, 9577506, 4359524, 15893864, 6291504, 12747392, 2140160, 5255168,
  1097728, 4390912, 1310720, 2621440]

end CertificateChecks.MonsterExist.ELevel

end
