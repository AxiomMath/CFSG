module

public import Certificates.Kernel.McL.MooreK
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Spor.PrimSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcL.Moore

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KS.Mathieu
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.McLCentralizer

theorem cent_eq {k : Nat} (hk : k < 30) : natArr (mclCentTbl k) = unpack 275 9 (MoCT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound MoCT.all (by norm_num) k hk
  rw [← MoCT.eq] at h
  exact h

theorem fix_eq : mclFix = fixL := by
  rw [← sel_spec fix_sel]
  unfold mclFix fixedList mclT0Arr
  apply List.filter_congr
  intro x hx
  have hx' : x < 275 := List.mem_range.1 hx
  rw [cent_eq (by norm_num), CFSG.KC.Misc.PairCount.unpack_get hx']
  cases h : Nat.beq (pg 9 (mask 9) (MoCT.F 4) x) x
  · have : pg 9 (mask 9) (MoCT.F 4) x ≠ x := fun e => by simp [e] at h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem fixL_nodup : fixL.Nodup := by
  rw [← sel_spec fix_sel]
  exact List.nodup_range.filter _

theorem fixL_len : fixL.length = 35 := rfl

theorem fixL_mem_lt {x : Nat} (hx : x ∈ fixL) : x < 275 := by
  rw [← sel_spec fix_sel] at hx
  exact List.mem_range.1 (List.mem_filter.1 hx).1

theorem fixL_lt {a : Nat} (ha : a < 35) : fixL[a]'(by rw [fixL_len]; exact ha) < 275 :=
  fixL_mem_lt (List.getElem_mem _)

theorem xg_facts {k : Nat} (hk : k < 2) : canonK 35 6 (mask 6) (35 * 6) (MoXG k) = true ∧
    ∀ a < 35, pg 9 (mask 9) (MoCT.F (Nat.add k 5)) (nget fixL a) =
      nget fixL (pg 6 (mask 6) (MoXG k) a) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec xg_ok k hk)
  exact ⟨h1, fun a ha => Nat.eq_of_beq_eq_true (allN_spec h2 a ha)⟩

theorem canon_lt {p a : Nat} (hp : canonK 35 6 (mask 6) (35 * 6) p = true) (ha : a < 35) :
    pg 6 (mask 6) p a < 35 := by
  have h' : bAnd(szOK 35 6, bAnd(Nat.beq (Nat.shiftRight p (35 * 6)) (nat_lit 0),
      allN 35 (fun i => Nat.blt (pg 6 (mask 6) p i) 35))) = true := hp
  simp only [bAnd_iff] at h'
  exact Eq.mp Nat.blt_eq (allN_spec h'.2.2 a ha)

theorem xgens_get {k : Nat} (hk : k < 2) : mclXGens[k]! = unpack 35 6 (MoXG k) := by
  obtain ⟨hc, hr⟩ := xg_facts hk
  rw [getElem!_pos mclXGens k (by simp [mclXGens]; omega)]
  simp only [mclXGens, Array.getElem_ofFn]
  rw [fix_eq, cent_eq (by omega)]
  apply Array.ext
  · simp [restrictArr, unpack, fixL_len]
  · intro a h1 _
    have ha : a < 35 := by simpa [restrictArr, fixL_len] using h1
    simp only [restrictArr, List.getElem_toArray, List.getElem_map]
    rw [CFSG.KC.Misc.PairCount.unpack_get (fixL_lt ha)]
    simp only [unpack, Array.getElem_ofFn]
    have e1 := hr a ha
    rw [nget_get fixL (by rw [fixL_len]; exact ha)] at e1
    have hb := canon_lt hc ha
    rw [nget_get fixL (by rw [fixL_len]; exact hb)] at e1
    have e2 : Nat.add k 5 = k + 5 := rfl
    rw [e2] at e1
    rw [e1, fixL_nodup.idxOf_getElem]

theorem mooreWord_lt (i : Nat) : ∀ j ∈ mooreWord i, j < 2 := by
  unfold mooreWord
  split <;> decide

theorem idc35 : canonK 35 6 (mask 6) (35 * 6) (pidn 35 6) = true ∧ idK 35 6 (mask 6) = true :=
  (bAnd_iff _ _).1 id35

theorem idc275 : canonK 275 9 (mask 9) (275 * 9) (pidn 275 9) = true ∧ idK 275 9 (mask 9) = true :=
  (bAnd_iff _ _).1 id275

theorem xP_eq (i : Nat) : mooreTab i = unpack 35 6 (xP i) ∧
    canonK 35 6 (mask 6) (35 * 6) (xP i) = true :=
  wordTabK_eq (idK_sound idc35.2).symm idc35.1 (mooreWord i) fun j hj =>
    ⟨xgens_get (mooreWord_lt i j hj), (xg_facts (mooreWord_lt i j hj)).1⟩

theorem liftP_eq : liftTab = unpack 275 9 liftP ∧ canonK 275 9 (mask 9) (275 * 9) liftP = true := by
  obtain ⟨c5, c6⟩ := (bAnd_iff (canonK 275 9 (mask 9) (275 * 9) (MoCT.F 5))
    (canonK 275 9 (mask 9) (275 * 9) (MoCT.F 6))).1 c275
  refine wordTabK_eq (idK_sound idc275.2).symm idc275.1 (mooreWord 4) fun j hj => ?_
  have hj2 : j < 2 := mooreWord_lt 4 j hj
  have e : Nat.add j 5 = j + 5 := rfl
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [getElem!_pos mclCTabs j (by simp [mclCTabs]; omega)]
    simp only [mclCTabs, Array.getElem_ofFn]
    exact cent_eq (by omega)
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact c5
    · exact c6

theorem comp_unpack {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    comp n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  compA_unpack hp hq

theorem sq_id {p : Nat} (hp : canonK 35 6 (mask 6) (35 * 6) p = true)
    (h : Nat.beq (pcomp 35 6 (mask 6) p p) (pidn 35 6) = true) :
    sqTab 35 (unpack 35 6 p) = idTab 35 := by
  rw [sqTab, comp_unpack hp hp, Nat.eq_of_beq_eq_true h]
  exact idK_sound idc35.2

theorem cube_id {p : Nat} (hp : canonK 35 6 (mask 6) (35 * 6) p = true)
    (h : Nat.beq (pcomp 35 6 (mask 6) p (pcomp 35 6 (mask 6) p p)) (pidn 35 6) = true) :
    cubeTab 35 (unpack 35 6 p) = idTab 35 := by
  rw [cubeTab, comp_unpack hp hp, comp_unpack hp (canonK_pcomp hp hp), Nat.eq_of_beq_eq_true h]
  exact idK_sound idc35.2

theorem moore_ok : mooreCheck = true := by
  have h2 := m2
  have h3 := m3
  simp only [List.all_eq_true, Bool.and_eq_true] at h2 h3
  unfold mooreCheck
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨?_, fun j hj => ⟨?_, ?_⟩⟩, fun i hi j hj => ?_⟩
  · rw [(xP_eq 1).1]
    exact cube_id (xP_eq 1).2 m1
  · rw [(xP_eq j).1]
    exact sq_id (xP_eq j).2 (h2 j hj).1
  · rw [(xP_eq (j - 1)).1, (xP_eq j).1, comp_unpack (xP_eq (j - 1)).2 (xP_eq j).2]
    exact cube_id (canonK_pcomp (xP_eq (j - 1)).2 (xP_eq j).2) (h2 j hj).2
  · rw [(xP_eq i).1, (xP_eq j).1, comp_unpack (xP_eq i).2 (xP_eq j).2]
    exact sq_id (canonK_pcomp (xP_eq i).2 (xP_eq j).2) (h3 i hi j hj)

theorem lift_ok : liftCheck = true := by
  unfold liftCheck
  rw [beq_iff_eq, liftP_eq.1, comp_unpack liftP_eq.2 liftP_eq.2, Nat.eq_of_beq_eq_true lift,
    mclT0Arr, cent_eq (by norm_num)]

theorem facts21000 : mooreCheck = true ∧ liftCheck = true := ⟨moore_ok, lift_ok⟩

end CertificateChecks.KernelMcL.Moore

end
