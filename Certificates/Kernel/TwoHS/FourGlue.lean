module

public import Certificates.Kernel.TwoHS.Four
public import Certificates.Kernel.HS3850.FusFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126
open CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.TwoHS

abbrev C3 (p : Nat) : Prop := canonK 3850 12 (mask 12) (3850 * 12) p = true

theorem rt_tab {k : Nat} (hk : k < 14) :
    hexT 3 3850 (3850 * k) harRHex = tabT (unpack 3850 12 (RT.F k)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound RT.all (by norm_num) k hk
  rw [← RT.eq] at h
  rw [← h, tabT_natArr]

theorem harRT_tab {c j : Nat} (h : 7 * c + j < 14) :
    harRT c j = tabT (unpack 3850 12 (RT.F (7 * c + j))) := rt_tab h

theorem invK_spec {p : Nat} (h : invK p = true) :
    C3 p ∧ C3 (pinv p) ∧ invEqK 3850 12 (mask 12) (3850 * 12) p (pinv p) = true := by
  unfold invK at h
  simp only [bAnd_iff] at h
  exact h

theorem perm_of {p : Nat} (h : invK p = true) :
    permOK 3850 (tabT (unpack 3850 12 p)) = true ∧
      invT 3850 (tabT (unpack 3850 12 p)) = tabT (unpack 3850 12 (pinv p)) ∧
      invOK 3850 (tabT (unpack 3850 12 p)) (invT 3850 (tabT (unpack 3850 12 p))) = true := by
  obtain ⟨c, ci, hi⟩ := invK_spec h
  have e := invT_unpack (by norm_num) hi
  refine ⟨permOK_unpack c hi, e, ?_⟩
  rw [e]
  exact invOK_unpack c ci hi

theorem sift_of {k : Nat}
    (hk : k < 14) (h : inPK k = true) : hsSift (tabT (unpack 3850 12 (RT.F k))) = true := by
  unfold inPK at h
  simp only [bAnd_iff] at h
  have hw : ∀ l ∈ rtW.getD k [], l < 16 := by
    have : ∀ j < 14, ∀ l ∈ rtW.getD j [], l < 16 := by decide
    exact this k hk
  obtain ⟨g, hg, hrep⟩ := CFSG.KD.LQT.HN.rep_word _ hw
  rw [← Nat.eq_of_beq_eq_true h.1] at hrep
  refine (CFSG.KD.LQT.HN.sift_iff (G := g) ?_).2 hg
  rw [natArr_tabT (invK_spec h.2).1]
  exact hrep

theorem conjOK_of {k r x : Nat}
    (hk : k < 14) (hin : inPK k = true) (hr : C3 r) (h : conjK (RT.F k) r x = true) :
    conjOK 3850 hsSift (tabT (unpack 3850 12 (RT.F k))) (tabT (unpack 3850 12 r))
      (tabT (unpack 3850 12 x)) = true := by
  have hs := sift_of hk hin
  have hi : invK (RT.F k) = true := by
    unfold inPK at hin
    simp only [bAnd_iff] at hin
    exact hin.2
  obtain ⟨c, ci, -⟩ := invK_spec hi
  obtain ⟨p1, e, p2⟩ := perm_of hi
  have hx : C3 x := by
    rw [← Nat.eq_of_beq_eq_true h]
    exact CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp c hr) ci
  unfold conjOK conjT
  rw [p1, p2, hs, e, compT_unpack c hr, compT_unpack (CFSG.KC.BfsPin.canonK_pcomp c hr) ci,
    tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp c hr) ci) hx]
  exact h

theorem wordB_eq {z y : Nat} (hz : C3 z) (hy : C3 y) {wd : List Nat}
    (hw : ∀ l ∈ wd, l = 1 ∨ l = 2) :
    wordTbl 3850 [tabT (unpack 3850 12 z), tabT (unpack 3850 12 y)] wd =
      tabT (unpack 3850 12 (wB z y wd)) ∧ C3 (wB z y wd) :=
  wordTbl_unpack CFSG.KD.HS3850.hid CFSG.KD.HS3850.hidc fun l hl => by
    rcases hw l hl with rfl | rfl
    · have e : lB z y 1 = z := by
        unfold lB
        rfl
      rw [e]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact ⟨trivial, hz⟩
    · have e : lB z y 2 = y := by
        unfold lB
        rfl
      rw [e]
      simp only [Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]
      exact ⟨trivial, hy⟩

theorem tComm_of {z y t : Nat} (hz : C3 z) (hy : C3 y) (ht : C3 t) {p : List Nat × List Nat}
    (hw1 : ∀ l ∈ p.1, l = 1 ∨ l = 2) (hw2 : ∀ l ∈ p.2, l = 1 ∨ l = 2) (h : commK z y p t = true) :
    tblEq 3850 (tComm 3850 (wordTbl 3850 [tabT (unpack 3850 12 z), tabT (unpack 3850 12 y)] p.1)
      (wordTbl 3850 [tabT (unpack 3850 12 z), tabT (unpack 3850 12 y)] p.2))
      (tabT (unpack 3850 12 t)) = true := by
  unfold commK at h
  simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff] at h
  obtain ⟨ha, hb, he⟩ := h
  obtain ⟨ea, ca⟩ := wordB_eq hz hy hw1
  obtain ⟨eb, cb⟩ := wordB_eq hz hy hw2
  obtain ⟨-, ia, -⟩ := perm_of ha
  obtain ⟨-, ib, -⟩ := perm_of hb
  have cai := (invK_spec ha).2.1
  have cbi := (invK_spec hb).2.1
  unfold tComm
  rw [ea, eb, ia, ib, compT_unpack ca cb, compT_unpack cai cbi,
    compT_unpack (CFSG.KC.BfsPin.canonK_pcomp ca cb) (CFSG.KC.BfsPin.canonK_pcomp cai cbi),
    tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp ca cb)
      (CFSG.KC.BfsPin.canonK_pcomp cai cbi)) ht]
  exact he

theorem commTT_of {a b : Nat} (ha : C3 a) (hb : C3 b) (h : Nat.beq (pc a b) (pc b a) = true) :
    commTT 3850 (tabT (unpack 3850 12 a)) (tabT (unpack 3850 12 b)) = true := by
  rw [commTT_unpack ha hb]
  exact h

theorem harFourOK_of {c : Nat}
    (hc : c < 2) (h : fourCK c = true) : harFourOK c = true := by
  unfold fourCK at h
  simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff, Nat.add_eq, Nat.mul_eq] at h
  obtain ⟨hr, hx, hin, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hin' : ∀ j < 6, inPK (7 * c + (j + 1)) = true := fun j hj => allN_spec hin j hj
  have i1 := hin' 0 (by norm_num)
  have i2 := hin' 1 (by norm_num)
  have i3 := hin' 2 (by norm_num)
  have i4 := hin' 3 (by norm_num)
  have i5 := hin' 4 (by norm_num)
  have i6 := hin' 5 (by norm_num)
  have hk : ∀ j < 7, 7 * c + j < 14 := fun j hj => by omega
  have cr := (invK_spec hr).1
  have cx := (invK_spec hx).1
  have cz : C3 (RT.F (7 * c + 3)) := (invK_spec ((bAnd_iff _ _).1 i3).2).1
  have cy : C3 (RT.F (7 * c + 4)) := (invK_spec ((bAnd_iff _ _).1 i4).2).1
  have c12 : C3 (HC.F 12) := CFSG.KD.HS3850.cent_cn (by norm_num)
  have c5 : C3 (HC.F 5) := CFSG.KD.HS3850.cent_cn (by norm_num)
  have hzi : invK (RT.F (7 * c + 3)) = true := ((bAnd_iff _ _).1 i3).2
  have hyi : invK (RT.F (7 * c + 4)) = true := ((bAnd_iff _ _).1 i4).2
  have hbp : ∀ c' < 2, ∀ k < 2, (∀ l ∈ ((harBPairs c').getD k ([], [])).1, l = 1 ∨ l = 2) ∧
      ∀ l ∈ ((harBPairs c').getD k ([], [])).2, l = 1 ∨ l = 2 := by decide
  have hlen : (harBPairs c).length = 2 := by
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> rfl
  unfold harFourOK harRho
  simp only []
  rw [harRT_tab (hk 0 (by norm_num)), harRT_tab (hk 1 (by norm_num)), harRT_tab (hk 2 (by norm_num)),
    harRT_tab (hk 3 (by norm_num)), harRT_tab (hk 4 (by norm_num)), harRT_tab (hk 5 (by norm_num)),
    harRT_tab (hk 6 (by norm_num)), Nat.add_zero, CFSG.KD.HS3850.cent_tab (by omega),
    CFSG.KD.HS3850.cent_tab (k := 12) (by norm_num), CFSG.KD.HS3850.cent_tab (k := 5) (by norm_num)]
  obtain ⟨pr1, -, pr2⟩ := perm_of hr
  obtain ⟨pz1, -, pz2⟩ := perm_of hzi
  obtain ⟨py1, -, py2⟩ := perm_of hyi
  have sz := sift_of (hk 3 (by norm_num)) i3
  have sy := sift_of (hk 4 (by norm_num)) i4
  have hrz : 7 * c + (2 + 1) = 7 * c + 3 := rfl
  have hry : 7 * c + (3 + 1) = 7 * c + 4 := rfl
  simp only [List.all_cons, List.all_nil, pr1, pr2, pz1, pz2, py1, py2, sz, sy,
    conjOK_of (hk 1 (by norm_num)) i1 c12 h1, commTT_of cx cr h2,
    conjOK_of (hk 2 (by norm_num)) i2 cr h3, commTT_of cz cr h4, commTT_of cy cr h5,
    hlen, List.getD_cons_zero, List.getD_cons_succ,
    tComm_of cz cy cz (hbp c hc 0 (by norm_num)).1 (hbp c hc 0 (by norm_num)).2 h6,
    tComm_of cz cy cy (hbp c hc 1 (by norm_num)).1 (hbp c hc 1 (by norm_num)).2 h7,
    conjOK_of (hk 5 (by norm_num)) i5 c5 h8,
    conjOK_of (hk 6 (by norm_num)) i6 cr h9, Bool.and_true, Bool.true_and, beq_self_eq_true,
    Nat.add_zero, CFSG.KD.HS3850.compT_pc cx cr, CFSG.KD.HS3850.compT_pc cr cz]

theorem harFourOK_true :
    harFourOK 0 = true ∧ harFourOK 1 = true :=
  ⟨harFourOK_of (by norm_num) four0, harFourOK_of (by norm_num) four1⟩

end CFSG.KD.TwoHS

end
