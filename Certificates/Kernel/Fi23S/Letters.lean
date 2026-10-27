module

public import Certificates.Kernel.Fi23S.ChkDefs
public import Certificates.Kernel.Fi23K.Letters
public import Certificates.Data.CFSGNative.Fi23.Classes
import Certificates.Kernel.Fi23S.Syl0
import Certificates.Kernel.Fi23S.Syl1
import Certificates.Kernel.Fi23S.Syl2
import Certificates.Kernel.Fi23S.Syl3
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib

public section

set_option maxRecDepth 400000

#kon_join CFSG.KD.Fi23S.sylAll CFSG.KD.Fi23S.sylF 16

namespace CertificateChecks.KernelFi23S

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23S CFSG.KD.Fi23K CFSG.KD.Fi23S
  CFSG.KS.Raw.Orb CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

theorem sylSl_spec {lo len : Nat} (h : sylSl lo len = true) :
    ∀ x, lo ≤ x → x < lo + len → x < 31671 → sylAt x = true := by
  intro x h1 h2 h3
  unfold sylSl at h
  have h' := allN_iff.1 h (x - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (x - lo) = x := by
    change lo + (x - lo) = x
    omega
  rw [e, bIf_eq, if_pos (Nat.blt_eq.mpr h3)] at h'
  exact h'

theorem syl_pt {x : Nat} (hx : x < 31671) : sylAt x = true := by
  have hs : x / 2048 < 16 := by omega
  have h : sylSl (x / 2048 * 2048) 2048 = true := sylAll (x / 2048) hs
  exact sylSl_spec h x (by omega) (by omega) hx

theorem sylJ_pt {x j : Nat} (hx : x < 31671) (hj : j < 21) :
    tb H (2 * j) x = wv G (SW.getD j []) x ∧ tb H (2 * j) x < 31671 ∧
      tb H (2 * j + 1) x < 31671 ∧ tb H (2 * j + 1) (tb H (2 * j) x) = x := by
  have h := syl_pt hx
  unfold sylAt at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  have h1 := allN_iff.1 h.1 j hj
  unfold sylJ sylJW at h1
  rw [strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, strictB_eq, bAnd_eq,
    Bool.and_eq_true] at h1
  obtain ⟨e1, e2, e3, e4⟩ := h1
  rw [Nat.blt_eq] at e2 e3
  exact ⟨Nat.eq_of_beq_eq_true e1, e2, e3, Nat.eq_of_beq_eq_true e4⟩

theorem xb_pt {x : Nat} (hx : x < 31671) : tb H 42 x = tb G 43 (tA G 1 x) := by
  have h := syl_pt hx
  unfold sylAt at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2.1

theorem xc_pt {x : Nat} (hx : x < 31671) : tb H 43 x = tb H 42 (tA G 39 x) := by
  have h := syl_pt hx
  unfold sylAt at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2.2

theorem sylWords_size : (sylWords ()).size = 21 := rfl

theorem sylWords_lt : ∀ j < 21, ∀ z ∈ (sylWords ())[j]!, 0 ≤ z ∧ z.toNat < 24 := by
  decide +kernel

theorem SW_eq : ∀ j < 21, SW.getD j [] = ((sylWords ())[j]!).map fun z => 52 + z.toNat := by
  decide +kernel

theorem foldr_LL : ∀ (w : List Int) (x : Nat),
    w.foldr (fun z y => LL z.toNat y) x = wv G (w.map fun z => 52 + z.toNat) x
  | [], _ => rfl
  | z :: w, x => by
    rw [List.foldr_cons, foldr_LL w x, List.map_cons]
    rfl

theorem LS_lt {l : Nat} (hl : l < 42) {x : Nat} (hx : x < 31671) : LS l x < 31671 := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j, l = 2 * j ∨ l = 2 * j + 1 := ⟨l / 2, by omega⟩
  · exact (sylJ_pt hx (by omega)).2.1
  · exact (sylJ_pt hx (by omega)).2.2.1

theorem LS_inv {j : Nat} (hj : j < 21) {x : Nat} (hx : x < 31671) :
    LS (2 * j + 1) (LS (2 * j) x) = x ∧ LS (2 * j) (LS (2 * j + 1) x) = x := by
  refine ⟨(sylJ_pt hx hj).2.2.2, ?_⟩
  exact right_inv_of_left (f := LS (2 * j)) (g := LS (2 * j + 1)) (fun y hy => (sylJ_pt hy hj).2.1)
    (fun y hy => (sylJ_pt hy hj).2.2.1) (fun y hy => (sylJ_pt hy hj).2.2.2) x hx

theorem syl_TR : (sylLetters (chainLetters orbLit)).size = 42 ∧
    ∀ l < 42, CFSG.KS.TW.TR 31671 (sylLetters (chainLetters orbLit))[l]! (LS l) := by
  have hs : (sylLetters (chainLetters orbLit)).size = 42 := by
    unfold sylLetters buildLetters
    rw [Array.size_ofFn, sylWords_size]
  refine ⟨hs, fun l hl => ?_⟩
  have e : (sylLetters (chainLetters orbLit))[l]! =
      (let t := wordT 31671 (jGen (chainLetters orbLit)) (sylWords ())[l / 2]!
       if l % 2 = 0 then t else invT 31671 t) := by
    unfold sylLetters buildLetters
    rw [getElem!_pos _ l (by rw [Array.size_ofFn, sylWords_size]; exact hl), Array.getElem_ofFn]
  have hw := CFSG.KS.TW.wordT_TR (n := 31671) (by norm_num) (gens := jGen (chainLetters orbLit))
    (G := fun z => LL z.toNat) ((sylWords ())[l / 2]!) fun z hz => by
      have hz' := (sylWords_lt (l / 2) (by omega) z hz).2
      unfold jGen
      exact letters_TR.2 _ hz'
  have hW : CFSG.KS.TW.TR 31671 (wordT 31671 (jGen (chainLetters orbLit)) (sylWords ())[l / 2]!)
      (LS (2 * (l / 2))) := by
    refine tr_congr hw fun x hx => ?_
    rw [foldr_LL, ← SW_eq _ (by omega)]
    exact (sylJ_pt hx (by omega)).1.symm
  rw [e]
  simp only
  split_ifs with h2
  · have e2 : 2 * (l / 2) = l := by omega
    rw [e2] at hW
    exact hW
  · have e2 : 2 * (l / 2) + 1 = l := by omega
    have hI := CFSG.KS.TW.invT_TR (n := 31671) (by norm_num) hW (g := LS (2 * (l / 2) + 1)) fun i hi =>
      ⟨LS_lt (by omega) hi, (LS_inv (by omega) hi).2, (LS_inv (by omega) hi).1⟩
    rw [e2] at hI
    exact hI

end CertificateChecks.KernelFi23S

end
