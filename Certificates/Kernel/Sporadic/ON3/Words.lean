
module

public import Certificates.Kernel.Sporadic.ON3.Defs
public import CFSG.Certificates.Kernel.Spor.PWord
public import CFSG.Sporadic.Schreier.ONCheckLocalInputs
public import Certificates.Kernel.Sporadic.ON.Minus2124

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KS.TW CFSG.KS.PW CFSG.KS.Words
open CertificateChecks.KernelSpor.ON (TT UU TT_lt UU_lt perm_facts' qon_eq')

theorem blt_of {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  simpa using h

theorem qon_size : qonStrongArrs.size = 7 := by
  rw [qon_eq', Array.size_ofFn]

theorem qon_get {j : Nat} (hj : j < 7) :
    qonStrongArrs[j]! = Array.ofFn (n := 245520) fun i => TT j i.val := by
  rw [qon_eq', getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem qon_letters : LettersOK 245520 7 qonStrongArrs qonInvArrs TT UU := by
  intro j hj x hx
  refine ⟨?_, ?_, TT_lt hx, UU_lt hx⟩
  · rw [qon_get hj]
    exact ofFn_get' (f := TT j) hx
  · unfold qonInvArrs pinvs
    rw [getElem!_pos _ j (by simpa [qon_size] using hj), Array.getElem_map,
      ← getElem!_pos qonStrongArrs j (by simpa [qon_size] using hj), qon_get hj]
    exact CFSG.KS.CB.pinvCand_get (fun y hy => TT_lt hy) (fun y hy => (perm_facts' y hy j hj).2.2) hx

@[expose] def Let7 (w : List Int) : Prop := ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 7

theorem wordArr_get {w : List Int} (hw : Let7 w) {x : Nat} (hx : x < 245520) :
    (wordArr w)[x]! = w.foldr (GZ TT UU) x ∧ w.foldr (GZ TT UU) x < 245520 :=
  pword_get qon_letters w hw x hx

theorem wordArr_eq {w : List Int} (hw : Let7 w) :
    wordArr w = Array.ofFn (n := 245520) fun i => w.foldr (GZ TT UU) i.val :=
  pword_eq qon_letters hw

theorem wordArrs_get {ws : Array (List Int)} {j : Nat} (hj : j < ws.size) :
    (wordArrs ws)[j]! = wordArr ws[j]! :=
  pwords_get hj

theorem trW_eq (k x : Nat) : trW k x = (decW (ON3W.WC k) (ON3W.WL k)).foldr (GZ TT UU) x :=
  trace_eq TT UU _ _ x

@[expose] def invW (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] def wordL : List (List Int) :=
  [Data.zWord, Data.centerGeneratorWord, Data.pairConjugatorWord,
    Data.intersectionWords[0]!, Data.intersectionWords[1]!, Data.intersectionWords[2]!,
    Data.intersectionWords[3]!, Data.MWords[1]!, Data.MWords[2]!, Data.LWords[0]!,
    Data.LWords[1]!, Data.TWords[0]!, Data.TWords[1]!, Data.TWords[2]!, Data.TWords[3]!,
    Data.TWords[4]!, Data.TWords[5]!, Data.TChain.strongWords[6]!, Data.TChain.strongWords[7]!,
    Data.MChain.strongWords[3]!, Data.MChain.strongWords[4]!, Data.LChain.strongWords[2]!,
    Data.LChain.strongWords[3]!]

theorem words_dec : ((List.range 23).all fun k =>
    decide (decW (ON3W.WC k) (ON3W.WL k) = wordL.getD k []) &&
      decide (decW (ON3W.WC (k + 23)) (ON3W.WL (k + 23)) = invW (wordL.getD k []))) = true := by
  decide +kernel

theorem dec_eq {k : Nat} (hk : k < 23) : decW (ON3W.WC k) (ON3W.WL k) = wordL.getD k [] := by
  have h := List.all_eq_true.1 words_dec k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem dec_inv {k : Nat} (hk : k < 23) :
    decW (ON3W.WC (k + 23)) (ON3W.WL (k + 23)) = invW (wordL.getD k []) := by
  have h := List.all_eq_true.1 words_dec k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem let7_all : ((List.range 17).all fun k =>
    (wordL.getD k []).all fun l => l != 0 && decide (l.natAbs ≤ 7)) = true := by
  decide +kernel

theorem let7 {k : Nat} (hk : k < 17) : Let7 (wordL.getD k []) := by
  intro l hl
  have h := List.all_eq_true.1 (List.all_eq_true.1 let7_all k (List.mem_range.2 hk)) l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact h

end CertificateChecks.KernelSpor.ON3

end
