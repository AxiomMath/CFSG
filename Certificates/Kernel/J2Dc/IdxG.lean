
module

public import Certificates.Kernel.J2Dc.IdxGCheck
public import Certificates.Kernel.J2Dc.Final
public import CFSG.Certificates.Kernel.S151IdxGSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J2Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.IdxF CFSG.KC.IdxG CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB.J2Lat CFSG.Quasithin.S151S9T
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.PP CFSG.KC.LQT.BC CFSG.KC.LQT.PW

theorem wW_img : ∀ (w : List ℕ) {p : ℕ}, p < 315 → imgW 9 (wW w) p = wordF L0 w p
  | [], p, hp => by
    change imgW 9 (ofFnW 315 9 fun i => i) p = p
    exact imgW_ofFnW (fun j hj => by omega) hp
  | l :: w, p, hp => by
    change imgW 9 (mulW 315 9 (J.tc.getD l 0) (wW w)) p = L0 l (wordF L0 w p)
    rw [mulW, imgW_ofFnW (fun j _ => imgW_lt _ _ _) hp, wW_img w hp, L0, tw_eq]

theorem good_congr {t : Array ℕ} {f g : ℕ → ℕ} (h : Good 315 t f) (e : ∀ p < 315, f p = g p) :
    Good 315 t g :=
  ⟨h.1, fun p hp => by rw [← e p hp]; exact h.2 p hp⟩

theorem good_T {l : ℕ} (hl : l < 8) : Good 315 (T l) (L0 l) := by
  rw [← tab_letter hl]
  exact good0 hl

theorem good_wW {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    Good 315 (wordTabL #[T 0, T 1] 315 w) (imgW 9 (wW w)) := by
  have hL : ∀ l < (#[T 0, T 1] : Array (Array ℕ)).size,
      Good 315 ((#[T 0, T 1] : Array (Array ℕ)).getD l #[]) (L0 l)
    | 0, _ => good_T (by decide)
    | 1, _ => good_T (by decide)
    | _ + 2, h => absurd h (by simp)
  have h := good_word hL (w := w) (fun l hl => by simpa using hw l hl)
  rw [wordTabA_eq_L] at h
  exact good_congr h fun p hp => (wW_img w hp).symm

theorem sT_eq : j2LatK.sTabs = [T 2, T 3, T 4] := T_eq.2.2.symm

theorem hyp : Hyp 315 j2LatK 5 3 (fun j => (J.mw.getD j []).length) (fun j l => imgW 9 (mc j l))
    (fun l => L0 (2 + l)) where
  nm_eq := mw_size
  ns_eq := by rw [sT_eq]; rfl
  len j hj := by rw [mt_get hj, List.length_map, mw_get]
  goodM j hj l hl := by
    rw [mLet_eq hj]
    unfold mLet
    have hs : sT.length = 3 := rfl
    by_cases h3 : l < 3
    · rw [CFSG.KC.IdxF.getD_append_left (by rw [hs]; exact h3)]
      have e : imgW 9 (mc j l) = L0 (2 + l) := by
        unfold mc
        rw [if_pos h3, L0, tw_eq]
      rw [e]
      interval_cases l
      · exact good_T (by decide)
      · exact good_T (by decide)
      · exact good_T (by decide)
    · obtain ⟨k, rfl⟩ : ∃ k, l = 3 + k := ⟨l - 3, by omega⟩
      have hk : k < ((J.mw.getD j []).map (wordTabL #[T 0, T 1] 315)).length := by
        have := hl
        rw [mLet_eq hj] at this
        unfold mLet at this
        simp only [List.size_toArray, List.length_append, hs] at this
        omega
      have e0 : (sT ++ (J.mw.getD j []).map (wordTabL #[T 0, T 1] 315)).toArray.getD (3 + k) #[] =
          ((J.mw.getD j []).map (wordTabL #[T 0, T 1] 315))[k] := CFSG.KC.IdxF.getD_append_right hk
      rw [e0, List.getElem_map]
      have e : mc j (3 + k) = wW ((J.mw.getD j []).getD k []) := by
        unfold mc
        rw [if_neg h3]
        congr 2
        omega
      have e1 : (J.mw.getD j []).getD k [] = (J.mw.getD j [])[k]'(by simpa using hk) :=
        List.getD_eq_getElem _ _ _
      rw [e, e1]
      exact good_wW (mw_lt2 _ (List.getElem_mem _))
  goodS l hl := by
    rw [sT_eq] at hl ⊢
    have hl3 : l < 3 := by simpa using hl
    interval_cases l
    · exact good_T (by decide)
    · exact good_T (by decide)
    · exact good_T (by decide)

theorem good_z : Good 315 j2SLP[143]! (imgW 9 zc) := by
  have h := good_node (j := 143) (by decide)
  rw [tab_node (by decide)] at h
  have e : zc = nodeK R 143 := by
    unfold zc R
    rw [eq_of_beq tcB]
    rfl
  rw [e]
  exact h

theorem j2K_checkG : j2Wit.Ok 315 (codeSetAct 315) j2Delta j2LatK j2SLP[143]! := by
  rw [delta_eq]
  exact idx3OkG_sound hyp (fun ht hf => fixCodes_sound codesB ht hf) good_z okG_j2

end CFSG.KD.J2Dc

end
