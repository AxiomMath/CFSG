module

public import Certificates.Kernel.G23F48.PtsCheck
public import CFSG.Certificates.Kernel.G23F48.PtsSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

theorem unpack_get {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [getElem!_pos (unpack n w P) i (by simp [unpack, hi])]
  simp [unpack]

private theorem bytes_get (b : ByteArray) (n : Nat) : b[n]! = b.get! n := by
  rcases b with ⟨bs⟩
  by_cases h : n < bs.size
  · rw [getElem!_pos (ByteArray.mk bs) n h]
    change bs[n] = bs[n]!
    rw [getElem!_pos bs n h]
  · rw [getElem!_neg (ByteArray.mk bs) n h]
    change default = bs[n]!
    rw [getElem!_neg bs n h]

private theorem fld_lt {k : Nat} (hk : k < 728) {j : Nat} (hj : j < 14) :
    pg 2 (mask 2) (PtsT.F k) j < 3 :=
  (ptNormK_spec ((ptsK_spec pts_ok).1 k hk)).2.1 j hj

theorem pts_eq {k : Nat} (hk : k < 728) : (burnsideF48t_g23Pts ())[k]! = unpack 14 2 (PtsT.F k) := by
  have hT := CFSG.KC.Misc.HexFlat.hexTable_sound PtsT.all k hk
  rw [← PtsT.eq] at hT
  unfold burnsideF48t_g23Pts
  rw [getElem!_pos _ k (by simpa using hk)]
  apply Array.ext (by simp [unpack])
  intro j h1 h2
  have hj : j < 14 := by simpa using h1
  simp only [Array.getElem_map, Array.getElem_range, unpack, Array.getElem_ofFn]
  have e := congrArg (fun a => a[j]!) hT
  simp only at e
  rw [unpack_get hj, getElem!_pos _ j (by simpa [CFSG.Monster.B.Co2.Native.hexTable] using hj)] at e
  simp only [CFSG.Monster.B.Co2.Native.hexTable, Array.getElem_ofFn,
    CFSG.Monster.B.Co2.Native.hexAt, CFSG.Monster.B.Co2.Native.hexVal, Nat.one_mul, Nat.add_zero,
    Nat.zero_mul, Nat.zero_add] at e
  have hl := fld_lt hk hj
  rw [bytes_get]
  split_ifs at e with hc
  · rw [e]
  · omega

theorem mats_eq {k : Nat} (hk : k < 4) : (burnsideF48t_g23Mats ())[k]! = unpack 196 2 (MP k) :=
  arrBind_sound (allN_spec m_bind k hk)

theorem gens_eq {k : Nat} (hk : k < 4) : (burnsideF48t_g23Gens ())[k]! = unpack 728 10 (GP k) :=
  arrBind_sound (allN_spec g_bind k hk)

theorem pts_norm {i : Nat} (hi : i < 728) : ((burnsideF48t_g23Pts ())[i]!).size = 14 ∧
    (∀ j < 14, ((burnsideF48t_g23Pts ())[i]!)[j]! < 3) ∧
    ∃ r < 14, (∀ s < r, ((burnsideF48t_g23Pts ())[i]!)[s]! = 0) ∧
      ((burnsideF48t_g23Pts ())[i]!)[r]! = 1 := by
  obtain ⟨-, ha, r, hr, hb, hc⟩ := ptNormK_spec ((ptsK_spec pts_ok).1 i hi)
  rw [pts_eq hi]
  refine ⟨by simp [unpack], fun j hj => ?_, r, hr, fun s hs => ?_, ?_⟩
  · rw [unpack_get hj]
    exact ha j hj
  · rw [unpack_get (by omega)]
    exact hb s hs
  · rw [unpack_get hr]
    exact hc

theorem pts_inj {i l : Nat} (hi : i < 728) (hl : l < 728)
    (h : (burnsideF48t_g23Pts ())[i]! = (burnsideF48t_g23Pts ())[l]!) : i = l := by
  rw [pts_eq hi, pts_eq hl] at h
  refine (ptsK_spec pts_ok).2 i hi l hl ?_
  have h0i := (ptNormK_spec ((ptsK_spec pts_ok).1 i hi)).1
  have h0l := (ptNormK_spec ((ptsK_spec pts_ok).1 l hl)).1
  refine CFSG.KS.PF.eq_of_fields (n := 14) (w := 2) (by decide) h0i h0l fun c hc => ?_
  have e : (unpack 14 2 (PtsT.F i))[c]! = (unpack 14 2 (PtsT.F l))[c]! := by rw [h]
  rwa [unpack_get hc, unpack_get hc] at e

theorem pts_ne_two {i l : Nat} (hi : i < 728) (hl : l < 728) :
    (burnsideF48t_g23Pts ())[i]! ≠ ((burnsideF48t_g23Pts ())[l]!).map fun x => 2 * x % 3 := by
  intro h
  obtain ⟨hsi, -, r, hr, hb, hc⟩ := pts_norm hi
  obtain ⟨hsl, -, t, ht, hb', hc'⟩ := pts_norm hl
  have hm : ∀ s < 14, ((burnsideF48t_g23Pts ())[i]!)[s]! =
      2 * ((burnsideF48t_g23Pts ())[l]!)[s]! % 3 := by
    intro s hs
    rw [h, getElem!_pos _ s (by simp [hsl, hs]), Array.getElem_map, getElem!_pos _ s (by omega)]
  rcases Nat.lt_trichotomy r t with h1 | h1 | h1
  · have := hm r hr
    rw [hc, hb' r h1] at this
    omega
  · have := hm r hr
    rw [hc, h1, hc'] at this
    omega
  · have := hm t ht
    rw [hb t h1, hc'] at this
    omega

private theorem find_lead {v : Array ℕ} {t c : ℕ} (ht : t < v.size) (h0 : ∀ s < t, v[s]! = 0)
    (hc : v[t]! = c) (hc0 : c ≠ 0) : v.find? (· != 0) = some c := by
  rw [Array.find?_eq_some_iff_getElem]
  refine ⟨by simpa using hc0, t, ht, by rw [← hc, getElem!_pos v t ht], fun j hj => ?_⟩
  have := h0 j hj
  rw [getElem!_pos v j (by omega)] at this
  simp [this]

theorem pts_basic {i : Nat} (hi : i < 728) : ((burnsideF48t_g23Pts ())[i]!).size = 14 ∧
    (((burnsideF48t_g23Pts ())[i]!).all fun x => decide (x < 3)) = true ∧
    ((burnsideF48t_g23Pts ())[i]!).find? (· != 0) = some 1 := by
  obtain ⟨hs, h3, r, hr, h0, h1⟩ := pts_norm hi
  refine ⟨hs, ?_, find_lead (by rw [hs]; exact hr) h0 h1 (by decide)⟩
  rw [Array.all_eq_true]
  intro j hj
  have := h3 j (by rw [hs] at hj; exact hj)
  rw [getElem!_pos _ j hj] at this
  simpa using this

private theorem mulVec_get {MA p r : Nat} (hr : r < 14) :
    (burnsideF48t_g23MulVec (unpack 196 2 MA) (unpack 14 2 p))[r]! = dotK MA p r % 3 := by
  unfold burnsideF48t_g23MulVec
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn, dotK_eq]
  have hm : ((List.range 14).map fun c => (unpack 196 2 MA)[14 * r + c]! * (unpack 14 2 p)[c]!) =
      (List.range 14).map fun c => pg 2 (mask 2) MA (14 * r + c) * pg 2 (mask 2) p c := by
    refine List.map_congr_left fun c hc => ?_
    rw [List.mem_range] at hc
    rw [unpack_get (by omega), unpack_get hc]
  simp only [burnsideF48t_g23Dot, Fin.val_mk]
  rw [hm]

theorem pts_gen {k i : ℕ} (hk : k < 4) (hi : i < 728) :
    ((burnsideF48t_g23Gens ())[k]!)[i]! < 728 ∧
      (burnsideF48t_g23Pts ())[((burnsideF48t_g23Gens ())[k]!)[i]!]! =
        burnsideF48t_g23Norm
          (burnsideF48t_g23MulVec (burnsideF48t_g23Mats ())[k]! (burnsideF48t_g23Pts ())[i]!) := by
  obtain ⟨hj, s, hs, hrow⟩ := genK_spec (gensK_spec gens_ok hk hi)
  rw [gens_eq hk, unpack_get hi, mats_eq hk, pts_eq hi, pts_eq hj]
  refine ⟨hj, ?_⟩
  obtain ⟨-, hlt, t, ht, hb, hc⟩ := ptNormK_spec ((ptsK_spec pts_ok).1 _ hj)
  have hsz : (burnsideF48t_g23MulVec (unpack 196 2 (MP k)) (unpack 14 2 (PtsT.F i))).size = 14 := by
    simp [burnsideF48t_g23MulVec]
  unfold burnsideF48t_g23Norm
  rcases hs with rfl | rfl
  · have hw : ∀ r < 14, (burnsideF48t_g23MulVec (unpack 196 2 (MP k)) (unpack 14 2 (PtsT.F i)))[r]! =
        pg 2 (mask 2) (PtsT.F (pg 10 (mask 10) (GP k) i)) r := by
      intro r hr
      rw [mulVec_get hr, hrow r hr, Nat.one_mul]
    have hf := find_lead (c := 1) (by rw [hsz]; exact ht)
      (fun s hs => by rw [hw s (by omega)]; exact hb s hs) (by rw [hw t ht]; exact hc) (by decide)
    rw [hf, if_neg (by decide)]
    apply Array.ext (by rw [hsz]; simp [unpack])
    intro r h1 h2
    have hr : r < 14 := by simpa [unpack] using h1
    rw [← getElem!_pos _ r h1, ← getElem!_pos _ r h2, hw r hr, unpack_get hr]
  · have hw : ∀ r < 14, (burnsideF48t_g23MulVec (unpack 196 2 (MP k)) (unpack 14 2 (PtsT.F i)))[r]! =
        2 * pg 2 (mask 2) (PtsT.F (pg 10 (mask 10) (GP k) i)) r % 3 := by
      intro r hr
      rw [mulVec_get hr, hrow r hr]
      omega
    have hf := find_lead (c := 2) (by rw [hsz]; exact ht)
      (fun s hs => by rw [hw s (by omega), hb s hs]) (by rw [hw t ht, hc]) (by decide)
    rw [hf, if_pos (by decide)]
    apply Array.ext (by rw [Array.size_map, hsz]; simp [unpack])
    intro r h1 h2
    have hr : r < 14 := by simpa [unpack] using h1
    rw [Array.getElem_map, ← getElem!_pos _ r h1]
    rw [← getElem!_pos _ r (by rw [hsz]; exact hr), hw r hr, unpack_get hr]
    have := hlt r hr
    omega

theorem frameIdx_lt : ∀ i < 15, frameIdx[i]! < 728 := by
  decide

theorem pts_frame : ∀ i < 15, (burnsideF48t_g23Pts ())[frameIdx[i]!]! = frameVecs[i]! := by
  intro i hi
  rw [pts_eq (frameIdx_lt i hi)]
  exact (arrBind_sound (allN_spec frame_bind i hi)).symm

end CFSG.KC.G23F48

end
