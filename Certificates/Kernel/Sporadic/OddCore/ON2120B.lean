module

public import Certificates.Kernel.Sporadic.OddCore.ON2120D

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2120

open CFSG.ONSchreier.Native hiding posArr
open CFSG.ONSchreier CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore
open CFSG.KS.TW CFSG.KS.PW CertificateChecks.KernelSpor.ON3 CFSG.KS
open CFSG.KC.Enum hiding pcomp
open CertificateChecks.KernelSpor.ON2119

@[expose] def b3 (F G : Nat → Nat) : Bool := [0, 227759, 100817].all fun b => Nat.beq (F b) (G b)

@[expose] noncomputable def hF (i x : Nat) : Nat := mG i x

@[expose] noncomputable def lwF (lwr : List (List Nat)) (j x : Nat) : Nat :=
  wordF 3 hF (lwr.getD j []) x

@[expose] def ex (a j : Nat) : Nat := if j = 0 then a / 16 else if j = 1 then a / 4 % 4 else a % 4

@[expose] noncomputable def candG (lwr : List (List Nat)) (a j x : Nat) : Nat :=
  lwF lwr j (Nat.repeat QT (ex a j) x)

@[expose] def let3 (w : List Nat) : Bool := w.all fun l => 1 ≤ l && l ≤ 3

@[expose] noncomputable def candP (lwr : List (List Nat)) (r : QuotRecord) (a : Nat) : Cand → Bool
  | .lift i => decide (i < r.lifts.length) && (List.range 3).all fun j =>
      b3 (wordF 3 hF ((r.lifts.getD i default).words.getD j [])) (candG lwr a j)
  | .rel w w' => let3 w && let3 w' &&
      [0, 227759, 100817].all (fun p => Nat.beq (wordF 3 hF w p) (wordF 3 hF w' p)) &&
      [0, 227759, 100817].any (fun p => !Nat.beq (wordF 3 (candG lwr a) w p)
        (wordF 3 (candG lwr a) w' p))

@[expose] noncomputable def blkP (F : Nat → Nat) (o : Nat) : Bool :=
  (List.range 120).all fun i =>
    decide (bw o i < 120) && inBlock Data.quotientBlocks[bw o i]! (F (Data.quotientBlocks[i]!)[0]!) &&
      inBlock Data.quotientBlocks[bw o i]! (F (Data.quotientBlocks[i]!)[1]!)

@[expose] noncomputable def piP (o : Nat) (T : Nat → Nat) : Bool :=
  (List.range 120).all fun x => Nat.beq Data.quotientConjugator[bw o (cil x)]! (T x)

@[expose] def pos120 (gs : Array (Array Nat)) (w : List Nat) (x : Nat) : Nat :=
  w.foldr (fun l y => (gs.getD (l - 1) (pid 120))[y]!) x

@[expose] noncomputable def candCheckP (r : QuotRecord) (lwr : List (List Nat)) (cs : List Cand)
    (k : Nat) : Bool :=
  lwr.length == 3 && lwr.all let3 &&
    (List.range 3).all (fun i => blkP (lwF lwr i) (3 * k + i) &&
      piP (3 * k + i) (pos120 #[qiArr r 0, qiArr r 1] piWords[i]!)) &&
    cs.length == 64 && (List.range 64).all fun a => candP lwr r a (cs.getD a default)

@[expose] noncomputable def headP (C : LocalCert) (L : LiftData) : Bool :=
  let3 L.qWord && b3 (wordF 3 hF L.qWord) QT &&
    (List.range 3).all (fun i => blkP (hF i) (36 + i) &&
      piP (36 + i) (pos120 #[C.quotGens.getD 0 #[], C.quotGens.getD 1 #[]] piWords[i]!)) &&
    L.lw.length == 12 && L.cands.length == 12

end CertificateChecks.KernelSpor.ON2120

end
