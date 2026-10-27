module

public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Kernel.HN1408.Words

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def cyHd (ws : List (List Nat)) (m cap : Nat) (G GI GJ T PL : Nat → Nat)
    (cnt : Nat) : Bool :=
  bAnd(allN ws.length fun j => bAnd(Nat.beq (GI j) (WK (ws.getD j [])),
    bAnd(Nat.beq (G j) idK, bAnd(canonK 1408 11 (mask 11) (1408 * 11) (GJ j),
      invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j)))),
    bAnd(Nat.beq cnt m, penumHdK idK cnt cap T PL))

@[expose] noncomputable def cyRec (K : Nat) (G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat)
    (cnt : Nat) : Bool :=
  bAnd(penumSlK 1408 11 (mask 11) (1408 * 11) true G GI K cnt T PL POS SRT SRI 0 cnt,
    bAnd(slK cnt (hsortPtK 1408 11 (mask 11) cnt T HS HSI) 0 cnt,
      slK (Nat.mul cnt (Nat.add K K)) (findPtK cnt T (prodQK 1408 11 (mask 11) (Nat.add K K) T
        (bothK K GI GJ)) CL) 0 (Nat.mul cnt (Nat.add K K))))

@[expose] noncomputable def cayCodes (mulC : Nat → Nat → Nat) (c1 : Nat) (tc : List Nat)
    (PL : Nat → Nat) (cnt : Nat) : List Nat :=
  (List.range' 1 (cnt - 1)).foldl
    (fun C k => C ++ [mulC (C.getD (parOf PL k) 0) (tc.getD (labOf PL k) 0)]) [c1]

@[expose] noncomputable def cayK (mulC : Nat → Nat → Nat) (c1 : Nat) (tc : List Nat) (K cnt : Nat)
    (PL CL : Nat → Nat) (C : List Nat) : Bool :=
  Nat.beq C.length cnt && Nat.beq (C.getD 0 0) c1 &&
    (List.range' 1 (cnt - 1)).all (fun k =>
      Nat.beq (C.getD k 0) (mulC (C.getD (parOf PL k) 0) (tc.getD (labOf PL k) 0))) &&
    (List.range cnt).all (fun k => (List.range K).all fun i =>
      Nat.beq (C.getD (r32 CL (k * (K + K) + i)) 0) (mulC (C.getD k 0) (tc.getD i 0))) &&
    decide C.Nodup

@[expose] def sl25Mul (x y : Nat) : Nat :=
  let a := x % 5
  let b := x / 5 % 5
  let c := x / 25 % 5
  let d := x / 125 % 5
  let a' := y % 5
  let b' := y / 5 % 5
  let c' := y / 25 % 5
  let d' := y / 125 % 5
  (a * a' + b * c') % 5 + 5 * ((a * b' + b * d') % 5) + 25 * ((c * a' + d * c') % 5) +
    125 * ((c * b' + d * d') % 5)

end CFSG.KD.HN1408

end
