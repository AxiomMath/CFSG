module

public import Certificates.Kernel.He7149.Checks
public import CFSG.Certificates.Kernel.E64FSound
public import CFSG.Certificates.Kernel.LocalQTBaseSRep
public import Certificates.Kernel.LocalQT.Base.C4141
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.He7149

open CFSG.KC.E64F CFSG.Quasithin.H13.KGE64 CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.LQT.BW.Pf

theorem good_of_rep {n w c : Nat} {t : Array Nat} (h : Rep n w c t) :
    Good n t (CFSG.KC.LQT.PW.imgW w c) :=
  ⟨h.1, fun p hp => ⟨(h.2 p hp).2.symm, by rw [(h.2 p hp).2]; exact (h.2 p hp).1⟩⟩

theorem slp_get : ∀ (l : List (Nat × Nat)) (arr : Array (Array Nat)) (i : Nat), i < arr.size →
    (l.foldl slpStepA arr)[i]! = arr[i]!
  | [], _, _, _ => rfl
  | p :: l, arr, i, hi => by
    rw [List.foldl_cons, slp_get l _ i (by simp [slpStepA]; omega)]
    unfold slpStepA
    rw [getElem!_pos (arr.push _) i (by simp; omega), getElem!_pos arr i hi,
      Array.getElem_push_lt hi]

theorem rep_he {j : Nat} (hj : j < heProg.length + 2) :
    Rep 8330 14 (CFSG.KD.LQT.C4141.TF j) heSLP[j]! := by
  have h := CFSG.KC.LQT.BS.baseSK_rep (by norm_num) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    CFSG.KD.LQT.C4141.hd CFSG.KD.LQT.C4141.N.all
  unfold heSLP
  rw [CFSG.KD.LQT.C4141.ta_eq, CFSG.KD.LQT.C4141.tb_eq]
  exact h.2 j (by rw [h.1]; exact hj)

theorem hSLPC : heSLPC = heSLP := by
  have hp : heProgC = heProg := by decide
  have ha : heTaC = heTa := rfl
  have hb : heTbC = heTb := rfl
  unfold heSLPC heSLP
  rw [hp, ha, hb]

theorem lt_eq : heE64Lt = #[heSLP[197]!, heSLP[207]!, heSLP[226]!, heSLP[247]!,
    wordTabA #[heTa, heTb] 8330 w7] := by
  have hq : heQpC = heQp := rfl
  have hm : heMwLit[7]! = [w7] := by decide
  have ha : heTaC = heTa := rfl
  have hb : heTbC = heTb := rfl
  unfold heE64Lt heSTabsC
  rw [hSLPC, hq, hm, ha, hb]
  rfl

theorem getD5_0 {α : Type} (a b c d e f : α) : #[a, b, c, d, e].getD 0 f = a := rfl
theorem getD5_1 {α : Type} (a b c d e f : α) : #[a, b, c, d, e].getD 1 f = b := rfl
theorem getD5_2 {α : Type} (a b c d e f : α) : #[a, b, c, d, e].getD 2 f = c := rfl
theorem getD5_3 {α : Type} (a b c d e f : α) : #[a, b, c, d, e].getD 3 f = d := rfl
theorem getD5_4 {α : Type} (a b c d e f : α) : #[a, b, c, d, e].getD 4 f = e := rfl

theorem good_lt : ∀ l < heE64Lt.size, Good 8330 (heE64Lt.getD l #[]) (LF l) := by
  have h := lt_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have hcode : ∀ {l j : Nat}, Nat.beq (TF l) (CFSG.KD.LQT.C4141.TF j) = true → j < heProg.length + 2 →
      ∀ {t : Array Nat}, t = heSLP[j]! → Good 8330 t (LF l) := by
    intro l j e hj t ht
    have eL : LF l = CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF j) := funext fun p => by
      unfold LF
      rw [Nat.eq_of_beq_eq_true e]
    rw [eL, ht]
    exact good_of_rep (rep_he hj)
  have hw4 : ∀ p < 8330, LF 4 p = wordF LAB w7 p := by
    have := w4_ok
    rw [List.all_eq_true] at this
    exact fun p hp => Nat.eq_of_beq_eq_true (this p (List.mem_range.2 hp))
  have hab : ∀ l < (#[heTa, heTb] : Array (Array Nat)).size,
      Good 8330 ((#[heTa, heTb] : Array (Array Nat)).getD l #[]) (LAB l) := by
    intro l hl
    have e0 : heSLP[0]! = heTa := by
      unfold heSLP slpTabsA
      rw [slp_get heProg _ 0 (by simp)]
      rfl
    have e1 : heSLP[1]! = heTb := by
      unfold heSLP slpTabsA
      rw [slp_get heProg _ 1 (by simp)]
      rfl
    rcases l with _ | _ | l
    · change Good 8330 heTa (CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF 0))
      rw [← e0]
      exact good_of_rep (rep_he (by decide))
    · change Good 8330 heTb (CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF 1))
      rw [← e1]
      exact good_of_rep (rep_he (by decide))
    · exact absurd hl (by simp)
  rw [lt_eq]
  intro l hl
  have hl5 : l < 5 := by simpa using hl
  obtain rfl | rfl | rfl | rfl | rfl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by omega
  · exact hcode h0 (by decide) (getD5_0 _ _ _ _ _ _)
  · exact hcode h1 (by decide) (getD5_1 _ _ _ _ _ _)
  · exact hcode h2 (by decide) (getD5_2 _ _ _ _ _ _)
  · exact hcode h3 (by decide) (getD5_3 _ _ _ _ _ _)
  · rw [getD5_4]
    have g := good_word hab (w := w7) (by decide)
    exact ⟨g.1, fun p hp => by rw [hw4 p hp]; exact g.2 p hp⟩

theorem e64 : e64Check 8330 heB ptAct heE64Lt heE64Y heE64O heLabels7 = true := by
  have hsz : heE64Lt.size = 5 := by
    rw [lt_eq]
    rfl
  have h := e64_ok
  rw [← hsz] at h
  exact e64_sound good_lt (by decide) (by decide +kernel) h

end CFSG.KD.He7149

end
