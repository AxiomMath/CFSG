module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.WitCheck
public import Certificates.Kernel.HN1408.Y442202Defs

public section

namespace CFSG.KD.HN1408.W441872

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KD.HN1408 CFSG.KD.HN1408.Y442202
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.CompatModel

@[expose] def vWords : List (List Nat) :=
  witConjB.map (fun h => h ++ wordB ++ h.reverse) ++
    witConjAZ.map (fun h => h ++ wordAZ ++ h.reverse)

@[expose] def vMode : List Nat := [1, 0, 1, 0, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2]

@[expose] def vSq : List (List Nat) :=
  [[], [], [], [], [], [], [4, 2, 7, 6, 1, 2], [2, 7, 3, 5, 7, 5], [3, 7, 1, 6, 5], [5, 3, 7, 4, 5],
    [3, 7, 4, 7, 5, 1], [3, 2, 3, 4, 1], [5, 1, 6, 4, 5, 2, 1], [3, 4, 7, 5, 3, 6, 1], [],
    [3, 4, 7, 5, 1]]

@[expose] noncomputable def gensInvK : Bool :=
  allN (nat_lit 7) (fun j => strictB (WK [Nat.add j (nat_lit 1)]) (fun g => Nat.beq (pc g g) idK))

@[expose] noncomputable def modeK (a az m : Nat) (g : List Nat) (p2 p4 : Nat) : Bool :=
  bIf(Nat.beq m (nat_lit 0), bIf(Nat.beq p4 idK, false, true),
    bIf(Nat.beq m (nat_lit 1), Nat.beq p2 a, conjInK (WK g) az p2))

@[expose] noncomputable def vertK (b a az m : Nat) (g : List Nat) (v : Nat) : Bool :=
  bAnd(bIf(commP v b, false, true), strictB (pc b v) (fun p => strictB (pc p p) (fun p2 =>
    strictB (pc p2 p2) (fun p4 => bAnd(bIf(Nat.beq (pc p4 p) idK, false, true),
      modeK a az m g p2 p4)))))

@[expose] noncomputable def vertsK (V : Nat → Nat) (M : List Nat) (S : List (List Nat)) : Bool :=
  strictB (WK wordB) (fun b => strictB (WK wordA) (fun a => strictB (WK wordAZ) (fun az =>
    allN (nat_lit 16) (fun j => vertK b a az (M.getD j (nat_lit 0)) (S.getD j []) (V j)))))

@[expose] noncomputable def vtK (V : Nat → Nat) : Bool :=
  allN (nat_lit 16) (fun j => Nat.beq (V j) (WK (vWords.getD j [])))

@[expose] noncomputable def covAt (V : Nat → Nat) (a b ab x c : Nat) : Bool :=
  bIf(Nat.blt c (nat_lit 16), commP (V c) x,
    bIf(involK x, bIf(Nat.beq x a, true, bIf(Nat.beq x b, true, Nat.beq x ab)), true))

@[expose] noncomputable def covK (T CV V : Nat → Nat) : Bool :=
  strictB (WK wordA) (fun a => strictB (WK wordB) (fun b => strictB (WK (wordA ++ wordB)) (fun ab =>
    allN (nat_lit 256) (fun i => strictB (T i) (fun x => covAt V a b ab x (CV i))))))

@[expose] noncomputable def centK (G : Nat → Nat) : Bool :=
  strictB (WK wordB) (fun b => allN (nat_lit 5) (fun j => commP (G j) b))

end CFSG.KD.HN1408.W441872

end
