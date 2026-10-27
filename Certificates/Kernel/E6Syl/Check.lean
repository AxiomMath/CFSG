module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylCheck
public import CFSG.Mathlib.Decide.Nodup

public section

namespace Certificates.Kernel.E6Syl

open CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.AGLEmbedding.R3

@[expose] def forceN {β : Sort _} (y : Nat) (k : Nat → β) : β :=
  Nat.rec (motive := fun _ => β) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] def forceL {β : Sort _} : List Nat → (List Nat → β) → β
  | [], k => k []
  | x :: l, k => forceN x fun x => forceL l fun l => k (x :: l)

@[expose] def forceLL {β : Sort _} : List (List Nat) → (List (List Nat) → β) → β
  | [], k => k []
  | l :: L, k => forceL l fun l => forceLL L fun L => k (l :: L)

@[expose] def dotF : List Nat → List Nat → Nat → Nat
  | x :: xs, y :: ys, acc => dotF xs ys (acc + x * y)
  | _, _, acc => acc

@[expose] def rows6 : List Nat → List (List Nat)
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: l => [a0, a1, a2, a3, a4, a5] :: rows6 l
  | _ => []

@[expose] def colsR (R : List (List Nat)) : List (List Nat) :=
  R.foldr (fun r C => List.zipWith List.cons r C) [[], [], [], [], [], []]

@[expose] def mmulF (A B : List Nat) : List Nat :=
  forceLL (colsR (rows6 B)) fun C => (rows6 A).flatMap fun r => C.map fun c => dotF r c 0 % 3

@[expose] def mpowF (A : List Nat) : Nat → List Nat
  | 0 => midL 3 6
  | e + 1 => mmulF A (mpowF A e)

@[expose] def wordsF : List (List Nat) → List (List Nat)
  | [] => [midL 3 6]
  | A :: As => (wordsF As).flatMap fun M => (List.range 3).map fun a => mmulF (mpowF A a) M

@[expose] def wordF (ω : List Nat) : List Nat :=
  ω.foldr (fun i A => mmulF (e6ReflL.getD i []) A) (midL 3 6)

@[expose] def gensF : List (List Nat) := e6SylWords.map wordF

@[expose] def matVecR (R : List (List Nat)) (v : List Nat) : List Nat :=
  R.map fun r => dotF r v 0 % 3

@[expose] def nfixR (V : List (List Nat)) (R : List (List Nat)) : Nat :=
  (V.filter fun v => matVecR R v == v).length

@[expose] def isO3F (I A : List Nat) : Bool :=
  A != I && mmulF (mmulF A A) A == I

@[expose] def memN (x : Nat) : List Nat → Bool
  | [] => false
  | y :: l => Nat.beq x y || memN x l

@[expose] def noncommF : List (List Nat) → Bool
  | t :: c :: _ => mmulF t c != mmulF c t
  | _ => false

@[expose] def boundsF (O : List Nat) : Bool :=
  O.all (fun n => decide (n ≤ 81)) && decide ((O.filter fun n => decide (27 < n)).length ≤ 25)

@[expose] def nfixesF (V : List (List Nat)) (I : List Nat) (S : List (List Nat)) : List Nat :=
  (S.filter (isO3F I)).map fun A => forceLL (rows6 A) (nfixR V)

@[expose] def chkCore (S G : List (List Nat)) (C : List Nat) (V : List (List Nat))
    (I : List Nat) : Bool :=
  S.length == 81 && CFSG.Decide.bitsetNodup (C.map (· % 100003)) &&
    G.all (fun A => S.all fun B => memN (codeL 3 (mmulF A B)) C) && noncommF G &&
    forceL (nfixesF V I S) boundsF

@[expose] def chk : Bool :=
  forceLL gensF fun G => forceLL (wordsF G) fun S => forceL (S.map (codeL 3)) fun C =>
    forceLL (allVecs 3 6) fun V => forceL (midL 3 6) fun I => chkCore S G C V I

theorem chk_ok : chk = true := by decide +kernel

end Certificates.Kernel.E6Syl
