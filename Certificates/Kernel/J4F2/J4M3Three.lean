module

public import Certificates.Data.J4M3.Three
public import Certificates.Kernel.J4F2.J4Std
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CertificateChecks.KernelJ4Q CFSG.Quasithin.J4M3

@[expose] noncomputable def pK (i : Nat) : Nat :=
  if i < 6 then eK (extraMasks.getD i 0) else wK (sWords.getD (i - 6) [])

@[expose] noncomputable def piK (i : Nat) : Nat :=
  if i < 6 then eK (extraMasks.getD i 0) else wK (invWord (sWords.getD (i - 6) []))

theorem pK_enc (i : Nat) : WfA (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i) ∧
    encR (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i) = pK i := by
  unfold pRows pK eR
  split
  · exact etaU_enc _
  · exact word_enc _

theorem piK_enc (i : Nat) :
    WfA (pInvRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i) ∧
      encR (pInvRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i) = piK i := by
  unfold pInvRows piK eR
  split
  · exact etaU_enc _
  · exact word_enc _

@[expose] noncomputable def commK (p x pi xi : Nat) : Nat := mulJ c rm (mulJ c rm (mulJ c rm p x) pi) xi

@[expose] noncomputable def qK (X Xi : Nat) (j : Nat) : Nat :=
  if j < 12 then commK (pK j) X (piK j) Xi else one

@[expose] noncomputable def a3K (q : Nat → Nat) (cm : Nat) : Nat :=
  (List.range 12).foldl (fun acc j => if cm.testBit j then mulJ c rm acc (q j) else acc) one

@[expose] noncomputable def chkY3K (X Xi Y : Nat) : Bool :=
  Nat.beq (mulJ c rm (mulJ c rm Y Y) Y) one &&
    v0Gens.all (fun cm => Nat.beq (mulJ c rm Y (eK cm)) (mulJ c rm (eK cm) Y)) &&
    (List.range 12).all fun i =>
      Nat.beq (mulJ c rm (a3K (qK X Xi) (a3Masks.getD i 0)) Y)
        (mulJ c rm (mulJ c rm (mulJ c rm (qK X Xi i) (eK (v3Masks.getD i 0))) Y)
          (a3K (qK X Xi) (a3Masks.getD i 0)))

theorem fold_enc {Q : Array (Array V2)} {q : Nat → Nat}
    (hQ : ∀ j, WfA (Q[j]?.getD (idRows ())) ∧ encR (Q[j]?.getD (idRows ())) = q j) (cm : Nat) :
    ∀ (L : List Nat) (acc : Array V2) (a : Nat), WfA acc ∧ encR acc = a →
      WfA (L.foldl (fun acc j => if cm.testBit j then mulRows acc (Q[j]?.getD idRows) else acc) acc) ∧
        encR (L.foldl (fun acc j => if cm.testBit j then mulRows acc (Q[j]?.getD idRows) else acc)
          acc) = L.foldl (fun acc j => if cm.testBit j then mulJ c rm acc (q j) else acc) a
  | [], _, _, h => h
  | j :: L, acc, a, h => by
    simp only [List.foldl_cons]
    apply fold_enc hQ cm L
    split
    · exact mkMul h (hQ j)
    · exact h

theorem a3_enc {Q : Array (Array V2)} {q : Nat → Nat}
    (hQ : ∀ j, WfA (Q[j]?.getD (idRows ())) ∧ encR (Q[j]?.getD (idRows ())) = q j) (cm : Nat) :
    WfA (a3Rows Q cm) ∧ encR (a3Rows Q cm) = a3K q cm :=
  fold_enc hQ cm _ _ _ mkId

theorem y3_ok : chkY3K (wK xWord) (wK (invWord xWord)) (wK y3Word) = true := by quickRfl

theorem chkY3_eq : chkY3 () = chkY3K (wK xWord) (wK (invWord xWord)) (wK y3Word) := by
  unfold chkY3 chkY3With chkY3K centV0
  simp only []
  have hX := word_enc xWord
  have hXi := word_enc (invWord xWord)
  have hY := word_enc y3Word
  have hQ : ∀ j, WfA ((((List.range 12).map fun j =>
      commRows (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) j)
        (pInvRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) j)
        (wordRows (locMats ()) (locInvs ()) xWord)
        (wordRows (locMats ()) (locInvs ()) (invWord xWord))).toArray)[j]?.getD (idRows ())) ∧
      encR ((((List.range 12).map fun j =>
      commRows (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) j)
        (pInvRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) j)
        (wordRows (locMats ()) (locInvs ()) xWord)
        (wordRows (locMats ()) (locInvs ()) (invWord xWord))).toArray)[j]?.getD (idRows ())) =
        qK (wK xWord) (wK (invWord xWord)) j := by
    intro j
    unfold qK
    by_cases hj : j < 12
    · simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj, Option.map_some,
        Option.getD_some, hj, if_true]
      exact mkMul (mkMul (mkMul (pK_enc j) hX) (piK_enc j)) hXi
    · have hn : ¬ j < ((List.range 12).map fun j =>
          commRows (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) j)
            (pInvRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) j)
            (wordRows (locMats ()) (locInvs ()) xWord)
            (wordRows (locMats ()) (locInvs ()) (invWord xWord))).length := by simpa using hj
      simp only [List.getElem?_toArray, List.getElem?_eq_none (Nat.le_of_not_lt hn),
        Option.getD_none, hj, if_false]
      exact mkId
  rw [mkEq (mkMul (mkMul hY hY) hY) mkId]
  congr 1
  · congr 1
    congr 1
    funext cm
    exact mkEq (mkMul hY (etaU_enc cm)) (mkMul (etaU_enc cm) hY)
  · apply mkRange_congr
    intro i _
    exact mkEq (mkMul (a3_enc hQ _) hY)
      (mkMul (mkMul (mkMul (hQ i) (etaU_enc _)) hY) (a3_enc hQ _))

open CFSG.Quasithin.J4M3 in
theorem c725101 : chkY3 () = true := chkY3_eq.trans y3_ok

end CertificateChecks.KernelJ4F2

end
