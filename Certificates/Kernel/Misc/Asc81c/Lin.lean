module

public import Certificates.Kernel.Misc.Asc81c.DataT

public section

namespace CertificateChecks.KernelAsc81c

open CFSG.Quasithin.Asc81c.Pf.Check CFSG.Monster.B.Co2.Native

@[expose] def idL (n : Nat) : List Nat := (List.range n).map (2 ^ ·)

@[expose] noncomputable def cmpL (n : Nat) (c d : List Nat) : List Nat := d.map (linVR n c)

@[expose] noncomputable def powL (n : Nat) (c : List Nat) : Nat → List Nat
  | 0 => idL n
  | e + 1 => cmpL n c (powL n c e)

@[expose] noncomputable def evalL(n : Nat) (a b : List Nat) : List Bool → List Nat
  | [] => idL n
  | false :: w => cmpL n a (evalL n a b w)
  | true :: w => cmpL n b (evalL n a b w)

@[expose] def eqL (n : Nat) (c d : List Nat) : Bool := (List.range n).all fun k => c.getD k 0 == d.getD k 0

@[expose] noncomputable def pow20L (n : Nat) (c : List Nat) : List Nat :=
  let p5 := cmpL n c (cmpL n (powL n c 2) (powL n c 2))
  let p10 := cmpL n p5 p5
  cmpL n p10 p10

@[expose] noncomputable def ord21L(n : Nat) (c : List Nat) : Bool := eqL n (cmpL n c (pow20L n c)) (idL n)

@[expose] noncomputable def conjL(n : Nat) (c x : List Nat) : List Nat := cmpL n c (cmpL n x (pow20L n c))

@[expose] noncomputable def meet3L (n : Nat) (x a b : List Nat) : Bool :=
  allLt (2 ^ n) fun i => !(linVR n x i == i && linVR n a i == i && linVR n b i == i) || i == 0

@[expose] noncomputable def ptWL(n : Nat) (x a b : List Nat) (w₁ w₂ v : List Bool) : Bool :=
  ord21L n (evalL n x a w₁) &&
    (ord21L n (evalL n x b w₂) &&
      !eqL n (cmpL n (conjL n (evalL n x a w₁) x) (conjL n (evalL n x b w₂) x))
        (cmpL n (conjL n (evalL n x b w₂) x) (conjL n (evalL n x a w₁) x)) &&
      !ord21L n (evalL n (conjL n (evalL n x a w₁) x) (conjL n (evalL n x b w₂) x) v))

@[expose] noncomputable def pairTL(n : Nat) (x a b : List Nat) (r : Nat) : Bool :=
  !meet3L n x a b ||
    (r % 4 == 1 && ptWL n x a b (decW 2 (r / 4 % 8)) (decW 2 (r / 32 % 8)) (decW 2 (r / 256 % 8))) ||
    (r % 4 == 2 && eqL n (evalL n x a (decW 6 (r / 4))) b)

@[expose] noncomputable def fixCountL (n : Nat) (c : List Nat) : Nat :=
  ((List.finRange (2 ^ n)).filter fun i => linVR n c i.val == i.val).length

@[expose] noncomputable def pre1L(n : Nat) (x c : List Nat) : Bool :=
  eqL n (powL n c 3) (idL n) && fixCountL n c == 2 ^ (n - 2) &&
    !eqL n (cmpL n x c) (cmpL n c x) && (wordsUpTo 4).all fun w => ord21L n (evalL n x c w)

@[expose] noncomputable def ord3L (n : Nat) (t : List Nat) : Bool := eqL n (powL n t 3) (idL n)

@[expose] noncomputable def fixLL (n : Nat) (t₁ t₂ : List Nat) : List Nat :=
  (List.range (2 ^ n)).filter fun i => linVR n t₁ i == i && linVR n t₂ i == i

@[expose] noncomputable def sumLL (n : Nat) (D : List Nat) (u : List Nat) : List Nat :=
  D.flatMap fun d => (List.range (2 ^ n)).map fun i => d ^^^ i ^^^ linVR n u i

@[expose] noncomputable def critL (n : Nat) (t₁ t₂ u : List Nat) : Bool :=
  (eqL n (cmpL n u u) (idL n) && !eqL n u (idL n)) && ord3L n t₁ && ord3L n t₂ &&
    bigEnough n (sumLL n (fixLL n t₁ t₂) u)

@[expose] noncomputable def genW2L (n : Nat) (x t t₁ : List Nat) (w₂ w : List Bool) : Bool :=
  ord3L n (evalL n x t w₂) &&
    decide (2 ≤ (fixLL n t₁ (evalL n x t w₂)).length) &&
    critL n t₁ (evalL n x t w₂) (evalL n t₁ (evalL n x t w₂) w)

@[expose] noncomputable def genWL (n : Nat) (x t : List Nat) (w₁ w₂ w : List Bool) : Bool :=
  ord3L n (evalL n x t w₁) && genW2L n x t (evalL n x t w₁) w₂ w

@[expose] noncomputable def pairWL (n : Nat) (x : List Nat) (c : List Nat) (r : Nat) : Bool :=
  !ord3G n c ||
    (!(fixCountL n c == 2 ^ (n - 2) &&
      allLt (2 ^ n) fun i => !(linVR n x i == i && linVR n c i == i) || i == 0) ||
      eqL n (cmpL n x c) (cmpL n c x) ||
      (r % 4 == 1 && critL n x c (evalL n x c (decW 10 (r / 4)))) ||
      (r % 4 == 2 && genWL n x c (decW 4 (r / 4 % 32)) (decW 4 (r / 128 % 32))
        (decW 4 (r / 4096 % 32))) ||
      (n == 3 && f21OK n (linAG n x) (linAG n c)))

@[expose] noncomputable def chunkL4 (d : Nat) : Bool :=
  allLt 16 fun a => allLt 16 fun b => allLt 16 fun c =>
    pairWL 4 (x0c 4) [a, b, c, d] (W (a + 16 * b + 256 * c + 4096 * d))

@[expose] noncomputable def chunkL3 (c : Nat) : Bool :=
  allLt 8 fun a => allLt 8 fun b => pairWL 3 (x0c 3) [a, b, c] (W (65536 + a + 8 * b + 64 * c))

@[expose] noncomputable def candL4 (d : Nat) : Bool :=
  allLt 16 fun a => allLt 16 fun b => allLt 16 fun c =>
    !ord3G 4 [a, b, c, d] ||
      (List.range 144).any (fun i => Nat.beq (WT i)
        (Nat.add a (Nat.mul 16 (Nat.add b (Nat.mul 16 (Nat.add c (Nat.mul 16 d))))))) ||
      !pre1L 4 (x0c 4) [a, b, c, d]

@[expose] noncomputable def candL3 : Bool :=
  allLt 8 fun a => allLt 8 fun b => allLt 8 fun c =>
    !ord3G 3 [a, b, c] ||
      (List.range 24).any (fun i => Nat.beq (WT (144 + i))
        (Nat.add a (Nat.mul 8 (Nat.add b (Nat.mul 8 c))))) ||
      !pre1L 3 (x0c 3) [a, b, c]

@[expose] noncomputable def rowL4 (i : Nat) : Bool :=
  (List.range 144).all fun j =>
    pairTL 4 (x0c 4) (decC 4 (WT i)) (decC 4 (WT j)) (WT (168 + 144 * i + j))

@[expose] noncomputable def rowL3 (i : Nat) : Bool :=
  (List.range 24).all fun j =>
    pairTL 3 (x0c 3) (decC 3 (WT (144 + i))) (decC 3 (WT (144 + j))) (WT (20904 + 24 * i + j))

end CertificateChecks.KernelAsc81c

end
