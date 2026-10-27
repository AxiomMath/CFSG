module

public import Certificates.Kernel.HN1408.M11Lem
public import Certificates.Data.Kernel.HN1408Blk

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.Blk

@[expose] noncomputable def shGensIn (K : Nat) (G T : Nat → Nat) (cnt : Nat) (P : Nat → Nat)
    (o : Nat) : Bool :=
  allN K fun j => bAnd(Nat.blt (r32 P (o + j)) cnt, Nat.beq (T (r32 P (o + j))) (G j))

@[expose] noncomputable def shNotIn (x : Nat) (T : Nat → Nat) (cnt : Nat) : Bool :=
  allN cnt fun i => bIf(Nat.beq (T i) x, false, true)

@[expose] noncomputable def shOrd (p x : Nat) : Bool :=
  bAnd(Nat.beq (ppK x p) idK, bIf(Nat.beq x idK, false, true))

@[expose] noncomputable def sh3K (r : Nat) (YG YT : Nat → Nat) (yc : Nat) (NG NT : Nat → Nat)
    (nc : Nat) (VG VT : Nat → Nat) (vc : Nat) (AG AT : Nat → Nat) (ac : Nat) (PY PN : Nat → Nat) :
    Bool :=
  bAnd(shOrd 3 r, bAnd(allN 3 (fun j => commP (YG j) r), bAnd(shNotIn r YT yc,
  bAnd(shGensIn 3 NG YT yc PY 0, bAnd(shGensIn 2 VG NT nc PN 0, bAnd(shGensIn 2 AG NT nc PN 2,
  bAnd(allN 2 (fun i => allN 3 fun j => commP (VG i) (NG j)),
  bAnd(allN vc (fun i => bIf(Nat.beq (VT i) idK, true, shNotIn (VT i) AT ac)),
    allN vc fun i => Nat.beq (pc (VT i) (VT i)) idK))))))))

@[expose] noncomputable def shNormK (C CI : Nat) (NG NT : Nat → Nat) (nc : Nat) (P : Nat → Nat)
    (o : Nat) : Bool :=
  bAnd(canonK 1408 11 (mask 11) (1408 * 11) CI, bAnd(invEqK 1408 11 (mask 11) (1408 * 11) C CI,
    allN 3 fun n => bAnd(Nat.blt (r32 P (o + 2 * n)) nc,
      bAnd(Nat.beq (NT (r32 P (o + 2 * n))) (pc (pc C (NG n)) CI),
      bAnd(Nat.blt (r32 P (o + 2 * n + 1)) nc,
        Nat.beq (NT (r32 P (o + 2 * n + 1))) (pc (pc CI (NG n)) C))))))

@[expose] noncomputable def sh5AK (r : Nat) (NG NT : Nat → Nat) (nc : Nat) (SG CW CI P : Nat → Nat) :
    Bool :=
  bAnd(allN 3 (fun j => commP (NG j) r), bAnd(allN 3 (fun j => commP (SG j) r),
  bAnd(allN nc (fun i => Nat.beq (ppK (NT i) 5) idK),
  bAnd(allN 4 (fun c => shNormK (CW c) (CI c) NG NT nc P (6 * c)),
    bIf(commP (NG 0) (NG 2), false, true)))))

@[expose] noncomputable def sh5CK (r : Nat) (YG YT : Nat → Nat) (yc : Nat) (P : Nat → Nat)
    (a u v UI VI B : Nat) : Bool :=
  bAnd(shOrd 5 r, bAnd(allN 2 (fun j => commP (YG j) r), bAnd(shNotIn r YT yc,
  bAnd(Nat.blt (r32 P 0) yc, bAnd(Nat.beq (YT (r32 P 0)) a,
  bAnd(Nat.blt (r32 P 1) yc, bAnd(Nat.beq (YT (r32 P 1)) u,
  bAnd(Nat.blt (r32 P 2) yc, bAnd(Nat.beq (YT (r32 P 2)) v,
  bAnd(blkTrivK 1408 11 4 B a,
  bAnd(canonK 1408 11 (mask 11) (1408 * 11) UI, bAnd(invEqK 1408 11 (mask 11) (1408 * 11) u UI,
  bAnd(canonK 1408 11 (mask 11) (1408 * 11) VI, bAnd(invEqK 1408 11 (mask 11) (1408 * 11) v VI,
    Nat.beq (pc (pc (pc u v) UI) VI) a))))))))))))))

@[expose] noncomputable def sh7K (r w a : Nat) (CG : Nat → Nat) : Bool :=
  bAnd(shOrd 7 r, bAnd(shOrd 2 w, bAnd(commP w r, bAnd(allN 2 (fun j => commP (CG j) w),
    bIf(Nat.beq w a, false, true)))))

@[expose] noncomputable def shLRec (k : Nat) (G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat)
    (cnt : Nat) : Bool :=
  bAnd(penumSlK k 4 (mask 4) (k * 4) true G GI 2 cnt T PL POS SRT SRI 0 cnt,
    bAnd(slK cnt (hsortPtK k 4 (mask 4) cnt T HS HSI) 0 cnt,
      slK (Nat.mul cnt 4) (findPtK cnt T (prodQK k 4 (mask 4) 4 T (bothK 2 GI GJ)) CL) 0
        (Nat.mul cnt 4)))

@[expose] noncomputable def shBlkK (B k : Nat) (ws : List (List Nat)) (LG : Nat → Nat) : Bool :=
  bAnd(blkLeK 1408 4 B k, bAnd(blkSurjK 1408 4 B k,
    allN 2 fun j => blkMapK 1408 11 4 B k (WK (ws.getD j [])) (LG j)))

@[expose] def zMul (n x y : Nat) : Nat := (x + y) % n

@[expose] def q8Mul (x y : Nat) : Nat :=
  if x < 4 then (if y < 4 then (x + y) % 4 else 4 + (y - x) % 4)
  else (if y < 4 then 4 + (x - 4 + y) % 4 else (y + 6 - x) % 4)

@[expose] def d10Mul (x y : Nat) : Nat :=
  if x < 5 then (if y < 5 then (x + y) % 5 else 5 + (y - x) % 5)
  else (if y < 5 then 5 + (x - 5 + y) % 5 else (y + 5 - x) % 5)

@[expose] def prodMul (b : Nat) (m1 m2 : Nat → Nat → Nat) (x y : Nat) : Nat :=
  m1 (x % b) (y % b) + b * m2 (x / b) (y / b)

@[expose] def s5Mul : Nat → Nat → Nat := prodMul 2 (zMul 2) q8Mul

@[expose] def b5Mul : Nat → Nat → Nat := prodMul 5 (zMul 5) (prodMul 2 (zMul 2) d10Mul)

end CFSG.KD.HN1408

end
