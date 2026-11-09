module

public import Certificates.Data.Kernel.Spor.ONTauK
public import Certificates.Kernel.Sporadic.ON2.Data
public import CFSG.Sporadic.Recognition.ONMultiplierInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal
public import Certificates.Kernel.Sporadic.ONC.RelsSplit
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KS.ONC CFSG.Sporadic.Recognition.ONMultiplier

@[expose] def onLetterIdx (z : Int) : Nat :=
  if 0 < z then (z - 1).toNat else (-z - 1).toNat + 4

@[expose] def seedInv (w : List Int) : List Int := (w.map Neg.neg).reverse

@[expose] def onGW : List (List Int) :=
  onGenWords.toList ++ onGenWords.toList.map seedInv ++ [[1], [2]]

@[expose] def onCheckPairs : List (List Nat × List Nat) :=
  onCheckWords.map (fun w => (w.map onLetterIdx, [])) ++
    [(onSurjA.map onLetterIdx, [8]), (onSurjB.map onLetterIdx, [9])]

set_option Elab.async false

#kc_natval OG0 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
  (onGW.getD (nat_lit 0) []) CFSG.KS.ONC.ONE

theorem cw0 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
    (onGW.getD (nat_lit 0) []) CFSG.KS.ONC.ONE) OG0 = true := by
  quickRfl

#kc_natval OG1 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
  (onGW.getD (nat_lit 1) []) CFSG.KS.ONC.ONE

theorem cw1 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
    (onGW.getD (nat_lit 1) []) CFSG.KS.ONC.ONE) OG1 = true := by
  quickRfl

#kc_natval OG2 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
  (onGW.getD (nat_lit 2) []) CFSG.KS.ONC.ONE

theorem cw2 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
    (onGW.getD (nat_lit 2) []) CFSG.KS.ONC.ONE) OG2 = true := by
  quickRfl

#kc_natval OG3 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
  (onGW.getD (nat_lit 3) []) CFSG.KS.ONC.ONE

theorem cw3 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
    (onGW.getD (nat_lit 3) []) CFSG.KS.ONC.ONE) OG3 = true := by
  quickRfl

#kc_natval OG4 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
  (onGW.getD (nat_lit 4) []) CFSG.KS.ONC.ONE

theorem cw4 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
    (onGW.getD (nat_lit 4) []) CFSG.KS.ONC.ONE) OG4 = true := by
  quickRfl

#kc_natval OG5 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
  (onGW.getD (nat_lit 5) []) CFSG.KS.ONC.ONE

theorem cw5 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
    (onGW.getD (nat_lit 5) []) CFSG.KS.ONC.ONE) OG5 = true := by
  quickRfl

#kc_natval OG6 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
  (onGW.getD (nat_lit 6) []) CFSG.KS.ONC.ONE

theorem cw6 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
    (onGW.getD (nat_lit 6) []) CFSG.KS.ONC.ONE) OG6 = true := by
  quickRfl

#kc_natval OG7 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
  (onGW.getD (nat_lit 7) []) CFSG.KS.ONC.ONE

theorem cw7 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
    (onGW.getD (nat_lit 7) []) CFSG.KS.ONC.ONE) OG7 = true := by
  quickRfl

#kc_natval OG8 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
  (onGW.getD (nat_lit 8) []) CFSG.KS.ONC.ONE

theorem cw8 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
    (onGW.getD (nat_lit 8) []) CFSG.KS.ONC.ONE) OG8 = true := by
  quickRfl

#kc_natval OG9 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
  (onGW.getD (nat_lit 9) []) CFSG.KS.ONC.ONE

theorem cw9 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI)
    (onGW.getD (nat_lit 9) []) CFSG.KS.ONC.ONE) OG9 = true := by
  quickRfl

theorem cwMap : onGW.map (fun w => CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI) w CFSG.KS.ONC.ONE) =
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9] := by
  rw [show onGW = [onGW.getD (nat_lit 0) [], onGW.getD (nat_lit 1) [], onGW.getD (nat_lit 2) [], onGW.getD (nat_lit 3) [], onGW.getD (nat_lit 4) [], onGW.getD (nat_lit 5) [], onGW.getD (nat_lit 6) [], onGW.getD (nat_lit 7) [], onGW.getD (nat_lit 8) [], onGW.getD (nat_lit 9) []] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [Nat.eq_of_beq_eq_true cw0, Nat.eq_of_beq_eq_true cw1, Nat.eq_of_beq_eq_true cw2, Nat.eq_of_beq_eq_true cw3, Nat.eq_of_beq_eq_true cw4, Nat.eq_of_beq_eq_true cw5, Nat.eq_of_beq_eq_true cw6, Nat.eq_of_beq_eq_true cw7, Nat.eq_of_beq_eq_true cw8, Nat.eq_of_beq_eq_true cw9]

theorem cp0 : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9]
    (List.take (nat_lit 6) (List.drop (nat_lit 0) onCheckPairs)) = true := by
  quickRfl

theorem cp1 : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9]
    (List.take (nat_lit 6) (List.drop (nat_lit 6) onCheckPairs)) = true := by
  quickRfl

theorem cp2 : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9]
    (List.take (nat_lit 5) (List.drop (nat_lit 12) onCheckPairs)) = true := by
  quickRfl

theorem cp3 : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9]
    (List.take (nat_lit 5) (List.drop (nat_lit 17) onCheckPairs)) = true := by
  quickRfl

theorem cp4 : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9]
    (List.take (nat_lit 5) (List.drop (nat_lit 22) onCheckPairs)) = true := by
  quickRfl

theorem cp5 : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9]
    (List.take (nat_lit 1) (List.drop (nat_lit 27) onCheckPairs)) = true := by
  quickRfl

theorem cp6 : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9]
    (List.take (nat_lit 1) (List.drop (nat_lit 28) onCheckPairs)) = true := by
  quickRfl

theorem cp7 : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9]
    (List.take (nat_lit 1) (List.drop (nat_lit 29) onCheckPairs)) = true := by
  quickRfl

theorem cp8 : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9]
    (List.take (nat_lit 1) (List.drop (nat_lit 30) onCheckPairs)) = true := by
  quickRfl

theorem cp9 : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    [OG0, OG1, OG2, OG3, OG4, OG5, OG6, OG7, OG8, OG9]
    (List.drop (nat_lit 31) onCheckPairs) = true := by
  quickRfl

theorem cpAll : CFSG.KS.ONC.pairsK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) CFSG.KS.ONC.ONE
    (onGW.map fun w => CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL ONSA ONSA ONSB ONSBI) w CFSG.KS.ONC.ONE)
    onCheckPairs = true := by
  rw [cwMap]
  exact (pairsK_seg onCheckPairs (nat_lit 0) (nat_lit 6) (nat_lit 6) rfl cp0
      (pairsK_seg onCheckPairs (nat_lit 6) (nat_lit 6) (nat_lit 12) rfl cp1
      (pairsK_seg onCheckPairs (nat_lit 12) (nat_lit 5) (nat_lit 17) rfl cp2
      (pairsK_seg onCheckPairs (nat_lit 17) (nat_lit 5) (nat_lit 22) rfl cp3
      (pairsK_seg onCheckPairs (nat_lit 22) (nat_lit 5) (nat_lit 27) rfl cp4
      (pairsK_seg onCheckPairs (nat_lit 27) (nat_lit 1) (nat_lit 28) rfl cp5
      (pairsK_seg onCheckPairs (nat_lit 28) (nat_lit 1) (nat_lit 29) rfl cp6
      (pairsK_seg onCheckPairs (nat_lit 29) (nat_lit 1) (nat_lit 30) rfl cp7
      (pairsK_seg onCheckPairs (nat_lit 30) (nat_lit 1) (nat_lit 31) rfl cp8
      cp9)))))))))

theorem checkWords_ok :
    relsK (fun j => List.getD ONW.LA j (nat_lit 0)) (fun j => List.getD ONW.LB j (nat_lit 0))
      onGW onCheckPairs = true :=
  relsK_of cA cB cBI ca1 cb1 cpAll

end CertificateChecks.KernelSpor.ONC

end
