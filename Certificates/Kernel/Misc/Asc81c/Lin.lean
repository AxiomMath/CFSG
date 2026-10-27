module

public import Certificates.Kernel.Misc.Asc81c.DataT

public section

namespace CertificateChecks.KernelAsc81c

open CFSG.Quasithin.Asc81c.Pf.Check CFSG.Monster.B.Co2.Native

@[expose] def idL (n : Nat) : List Nat := (List.range n).map (2 ^ ·)

@[expose] def cmpL (n : Nat) (c d : List Nat) : List Nat := d.map (linV n c)

@[expose] def powL (n : Nat) (c : List Nat) : Nat → List Nat
  | 0 => idL n
  | e + 1 => cmpL n c (powL n c e)

@[expose] def evalL (n : Nat) (a b : List Nat) : List Bool → List Nat
  | [] => idL n
  | false :: w => cmpL n a (evalL n a b w)
  | true :: w => cmpL n b (evalL n a b w)

@[expose] def eqL (n : Nat) (c d : List Nat) : Bool := (List.range n).all fun k => c.getD k 0 == d.getD k 0

@[expose] def ord21L (n : Nat) (c : List Nat) : Bool := eqL n (powL n c 21) (idL n)

@[expose] def conjL (n : Nat) (c x : List Nat) : List Nat := cmpL n c (cmpL n x (powL n c 20))

@[expose] def meet3L (n : Nat) (x a b : List Nat) : Bool :=
  allLt (2 ^ n) fun i => !(linV n x i == i && linV n a i == i && linV n b i == i) || i == 0

@[expose] def ptWL (n : Nat) (x a b : List Nat) (w₁ w₂ v : List Bool) : Bool :=
  ord21L n (evalL n x a w₁) &&
    (ord21L n (evalL n x b w₂) &&
      !eqL n (cmpL n (conjL n (evalL n x a w₁) x) (conjL n (evalL n x b w₂) x))
        (cmpL n (conjL n (evalL n x b w₂) x) (conjL n (evalL n x a w₁) x)) &&
      !ord21L n (evalL n (conjL n (evalL n x a w₁) x) (conjL n (evalL n x b w₂) x) v))

@[expose] def pairTL (n : Nat) (x a b : List Nat) (r : Nat) : Bool :=
  !meet3L n x a b ||
    (r % 4 == 1 && ptWL n x a b (decW 2 (r / 4 % 8)) (decW 2 (r / 32 % 8)) (decW 2 (r / 256 % 8))) ||
    (r % 4 == 2 && eqL n (evalL n x a (decW 6 (r / 4))) b)

@[expose] def fixCountL (n : Nat) (c : List Nat) : Nat :=
  ((List.finRange (2 ^ n)).filter fun i => linV n c i.val == i.val).length

@[expose] def pre1L (n : Nat) (x c : List Nat) : Bool :=
  eqL n (powL n c 3) (idL n) && fixCountL n c == 2 ^ (n - 2) &&
    !eqL n (cmpL n x c) (cmpL n c x) && (wordsUpTo 4).all fun w => ord21L n (evalL n x c w)

@[expose] noncomputable def candL4 (d : Nat) : Bool :=
  allLt 16 fun a => allLt 16 fun b => allLt 16 fun c =>
    !ord3V 4 [a, b, c, d] || (List.range 144).any (fun i => decC 4 (WT i) == [a, b, c, d]) ||
      !pre1L 4 (x0c 4) [a, b, c, d]

@[expose] noncomputable def candL3 : Bool :=
  allLt 8 fun a => allLt 8 fun b => allLt 8 fun c =>
    !ord3V 3 [a, b, c] || (List.range 24).any (fun i => decC 3 (WT (144 + i)) == [a, b, c]) ||
      !pre1L 3 (x0c 3) [a, b, c]

@[expose] noncomputable def rowL4 (i : Nat) : Bool :=
  (List.range 144).all fun j =>
    pairTL 4 (x0c 4) (decC 4 (WT i)) (decC 4 (WT j)) (WT (168 + 144 * i + j))

@[expose] noncomputable def rowL3 (i : Nat) : Bool :=
  (List.range 24).all fun j =>
    pairTL 3 (x0c 3) (decC 3 (WT (144 + i))) (decC 3 (WT (144 + j))) (WT (20904 + 24 * i + j))

end CertificateChecks.KernelAsc81c

end
