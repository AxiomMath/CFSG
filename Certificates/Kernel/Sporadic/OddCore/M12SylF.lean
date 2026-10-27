module

public import Certificates.Kernel.Sporadic.OddCore.M12Syl
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.M12Syl

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.MulH CFSG.KC.BfsPin CFSG.GH74.Generic.S45.EvSpor

theorem evalWord_foldl {n w : Nat} {gs : Array Table} {S : Nat → Nat} :
    ∀ (wd : List Nat) (acc : Nat), canonK n w (mask w) (n * w) acc = true →
      (∀ l ∈ wd, (if l < gs.size then gs[l]! else invT n gs[l - gs.size]!) =
          tabT (unpack n w (S l)) ∧ canonK n w (mask w) (n * w) (S l) = true) →
      wd.foldl (fun a i => compT n a (if i < gs.size then gs[i]! else invT n gs[i - gs.size]!))
          (tabT (unpack n w acc)) = tabT (unpack n w (wfoldK n w (mask w) S wd acc)) ∧
        canonK n w (mask w) (n * w) (wfoldK n w (mask w) S wd acc) = true
  | [], acc, ha, _ => ⟨rfl, ha⟩
  | l :: rest, acc, ha, h => by
    obtain ⟨h1, h2⟩ := h l List.mem_cons_self
    rw [List.foldl_cons, h1, compT_unpack ha h2, wfoldK_cons]
    exact evalWord_foldl rest _ (canonK_pcomp ha h2) fun l' hl' =>
      h l' (List.mem_cons_of_mem l hl')

theorem base : szOK 24 5 = true ∧ canonK 24 5 (mask 5) (24 * 5) (pidn 24 5) = true ∧
    CFSG.KS.Prim.idK 24 5 (mask 5) = true ∧
    (∀ j < 4, canonK 24 5 (mask 5) (24 * 5) (M12L j) = true) ∧
    (∀ j < 4, canonK 24 5 (mask 5) (24 * 5) (M12SI j) = true) ∧
    invEqK 24 5 (mask 5) (24 * 5) (M12L 0) (M12L 2) = true ∧
    invEqK 24 5 (mask 5) (24 * 5) (M12L 1) (M12L 3) = true ∧
    (∀ j < 4, invEqK 24 5 (mask 5) (24 * 5) (M12S.GI j) (M12SI j) = true) ∧
    (∀ j < 4, M12S.G j = pidn 24 5) ∧
    M12S.GI 0 = wfoldK 24 5 (mask 5) M12L m12WA (pidn 24 5) ∧
    M12S.GI 1 = wfoldK 24 5 (mask 5) M12L m12WB (pidn 24 5) ∧
    M12S.GI 2 = wfoldK 24 5 (mask 5) M12L m12WY (pidn 24 5) ∧
    M12S.GI 3 = wfoldK 24 5 (mask 5) M12L m12WX (pidn 24 5) ∧
    M12S.cnt = 64 ∧ penumHdK (pidn 24 5) M12S.cnt 3000 M12S.T M12S.PL = true := by
  have h := base_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, c1, c2⟩ := h
  exact ⟨a1, a2, a3, allN_spec a4, allN_spec a5, a6, a7, allN_spec a8,
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec a9 j hj), Nat.eq_of_beq_eq_true b0,
    Nat.eq_of_beq_eq_true b1, Nat.eq_of_beq_eq_true b2, Nat.eq_of_beq_eq_true b3,
    Nat.eq_of_beq_eq_true c1, c2⟩

theorem hn : szOK 24 5 = true := base.1

theorem hidc : canonK 24 5 (mask 5) (24 * 5) (pidn 24 5) = true := base.2.1

theorem hid : idT 24 = tabT (unpack 24 5 (pidn 24 5)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem lc {j : Nat} (hj : j < 4) : canonK 24 5 (mask 5) (24 * 5) (M12L j) = true :=
  base.2.2.2.1 j hj

theorem sic {j : Nat} (hj : j < 4) : canonK 24 5 (mask 5) (24 * 5) (M12SI j) = true :=
  base.2.2.2.2.1 j hj

theorem a1_tab : m12A1T = tabT (unpack 24 5 (M12L 0)) := by
  rw [← tabs_eq.1, tabT_natArr]

theorem b1_tab : m12B1T = tabT (unpack 24 5 (M12L 1)) := by
  rw [← tabs_eq.2, tabT_natArr]

theorem letter_ok {l : Nat} (hl : l < 4) :
    (if l < m12DGens.size then m12DGens[l]! else invT 24 m12DGens[l - m12DGens.size]!) =
      tabT (unpack 24 5 (M12L l)) ∧ canonK 24 5 (mask 5) (24 * 5) (M12L l) = true := by
  refine ⟨?_, lc hl⟩
  have hs : m12DGens.size = 2 := rfl
  rw [hs]
  interval_cases l
  · exact a1_tab
  · exact b1_tab
  · change invT 24 m12A1T = _
    rw [a1_tab, invT_unpack (by norm_num) base.2.2.2.2.2.1]
  · change invT 24 m12B1T = _
    rw [b1_tab, invT_unpack (by norm_num) base.2.2.2.2.2.2.1]

theorem word_tab {wd : List Nat} (hw : ∀ l ∈ wd, l < 4) :
    evalWord 24 m12DGens wd = tabT (unpack 24 5 (wfoldK 24 5 (mask 5) M12L wd (pidn 24 5))) ∧
      canonK 24 5 (mask 5) (24 * 5) (wfoldK 24 5 (mask 5) M12L wd (pidn 24 5)) = true := by
  unfold evalWord
  rw [hid]
  exact evalWord_foldl wd _ hidc fun l hl => letter_ok (hw l hl)

theorem m12_tabs : (m12TA = tabT (unpack 24 5 (M12S.GI 0)) ∧
      canonK 24 5 (mask 5) (24 * 5) (M12S.GI 0) = true) ∧
    (m12TB = tabT (unpack 24 5 (M12S.GI 1)) ∧ canonK 24 5 (mask 5) (24 * 5) (M12S.GI 1) = true) ∧
    (m12TY = tabT (unpack 24 5 (M12S.GI 2)) ∧ canonK 24 5 (mask 5) (24 * 5) (M12S.GI 2) = true) ∧
    (m12TX = tabT (unpack 24 5 (M12S.GI 3)) ∧
      canonK 24 5 (mask 5) (24 * 5) (M12S.GI 3) = true) := by
  obtain ⟨e0, e1, e2, e3, -⟩ := base.2.2.2.2.2.2.2.2.2
  rw [e0, e1, e2, e3]
  exact ⟨word_tab (by decide), word_tab (by decide), word_tab (by decide), word_tab (by decide)⟩

theorem s_tabs : TabsOK 24 5 4 M12S.GI [m12TA, m12TB, m12TY, m12TX].toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨y1, y2⟩, ⟨x1, x2⟩⟩ := m12_tabs
  interval_cases j
  · exact ⟨by rw [← a1]; rfl, a2⟩
  · exact ⟨by rw [← b1]; rfl, b2⟩
  · exact ⟨by rw [← y1]; rfl, y2⟩
  · exact ⟨by rw [← x1]; rfl, x2⟩

theorem s_invs : ∀ j < 4, invEqK 24 5 (mask 5) (24 * 5) (M12S.GI j) (M12SI j) = true ∧
    canonK 24 5 (mask 5) (24 * 5) (M12SI j) = true :=
  fun j hj => ⟨base.2.2.2.2.2.2.2.1 j hj, sic hj⟩

theorem s_pe : ∀ i < M12S.cnt, penumPtK 24 5 (mask 5) (24 * 5) true M12S.G M12S.GI 4 M12S.cnt
    M12S.T M12S.PL M12S.POS M12S.SRT M12S.SRI i = true :=
  fun i hi => penumSl_spec sE i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < M12S.cnt, hsortPtK 24 5 (mask 5) M12S.cnt M12S.T M12S.HS M12S.HSI i = true :=
  fun i hi => slK_spec sH i (Nat.zero_le _) (by omega) hi

theorem s_cl : ∀ c < M12S.cnt * (4 + 4), findPtK M12S.cnt M12S.T
    (prodQK 24 5 (mask 5) (4 + 4) M12S.T (bothK 4 M12S.GI M12SI)) M12Cl c = true :=
  fun c hc => slK_spec sCl c (Nat.zero_le _) (by change c < Nat.mul M12S.cnt 8; omega)
    (by change c < Nat.mul M12S.cnt 8; omega)

theorem evEnum_of {n cp sz : Nat} {gs : List Table}
    (h1 : CFSG.Sporadic.SmallOddCore.enumOK n cp sz gs = true)
    (h2 : gs.all (fun g => CFSG.Sporadic.SmallOddCore.permOK n g) = true) :
    CFSG.GH74.Generic.S45.EvSpor.enumOK n cp gs sz = true := by
  unfold CFSG.Sporadic.SmallOddCore.enumOK at h1
  unfold CFSG.GH74.Generic.S45.EvSpor.enumOK
  simp only [Bool.and_eq_true, List.all_eq_true] at h1 h2 ⊢
  obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩ := h1
  exact ⟨⟨⟨⟨fun g hg => ⟨h2 g hg, ha g hg⟩, hb⟩, hc⟩, hd⟩, he⟩

theorem enum_ok : CFSG.GH74.Generic.S45.EvSpor.enumOK 24 cap [m12TA, m12TB, m12TY, m12TX] 64 =
    true := by
  refine evEnum_of (enumOK_of hn base.2.2.2.2.2.2.2.2.1 s_tabs s_invs base.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    s_pe s_hs s_cl base.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  rw [List.all_eq_true]
  intro g hgm
  obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list s_tabs hgm
  exact permOK_unpack hc (s_invs j hj).1

theorem rels : Nat.beq (pc (M12S.GI 0) (pc (M12S.GI 0) (pc (M12S.GI 0) (pc (M12S.GI 0) idK)))) idK =
      true ∧
    Nat.beq (pc (M12S.GI 1) (pc (M12S.GI 1) (pc (M12S.GI 1) (pc (M12S.GI 1) idK)))) idK = true ∧
    Nat.beq (pc (M12S.GI 0) (M12S.GI 1)) (pc (M12S.GI 1) (M12S.GI 0)) = true ∧
    Nat.beq (pc (M12S.GI 2) (M12S.GI 2)) idK = true ∧
    Nat.beq (pc (M12S.GI 3) (M12S.GI 3)) idK = true ∧
    Nat.beq (pc (M12S.GI 2) (M12S.GI 3)) (pc (M12S.GI 3) (M12S.GI 2)) = true ∧
    Nat.beq (pc (pc (M12S.GI 2) (M12S.GI 0)) (M12SI 2)) (M12S.GI 1) = true ∧
    Nat.beq (pc (pc (M12S.GI 2) (M12S.GI 1)) (M12SI 2)) (M12S.GI 0) = true ∧
    Nat.beq (pc (pc (M12S.GI 3) (M12S.GI 0)) (M12SI 3)) (M12SI 0) = true ∧
    Nat.beq (pc (pc (M12S.GI 3) (M12S.GI 1)) (M12SI 3)) (M12SI 1) = true := by
  simpa only [bAnd_iff] using rels_ok

theorem pow4_unpack {p : Nat} (hp : canonK 24 5 (mask 5) (24 * 5) p = true) :
    tblEq 24 (powT 24 4 (tabT (unpack 24 5 p))) (idT 24) =
      Nat.beq (pc p (pc p (pc p (pc p idK)))) idK := by
  have e : powT 24 4 (tabT (unpack 24 5 p)) = compT 24 (tabT (unpack 24 5 p))
      (compT 24 (tabT (unpack 24 5 p)) (compT 24 (tabT (unpack 24 5 p))
        (compT 24 (tabT (unpack 24 5 p)) (idT 24)))) := rfl
  have c1 := canonK_pcomp hp hidc
  have c2 := canonK_pcomp hp c1
  have c3 := canonK_pcomp hp c2
  rw [e, hid, compT_unpack hp hidc, compT_unpack hp c1, compT_unpack hp c2, compT_unpack hp c3,
    tblEq_unpack (canonK_pcomp hp c3) hidc]
  rfl

theorem sq_unpack {p : Nat} (hp : canonK 24 5 (mask 5) (24 * 5) p = true) :
    tblEq 24 (compT 24 (tabT (unpack 24 5 p)) (tabT (unpack 24 5 p))) (idT 24) =
      Nat.beq (pc p p) idK := by
  rw [hid, compT_unpack hp hp, tblEq_unpack (canonK_pcomp hp hp) hidc]
  rfl

theorem conj_unpack {g gi x y : Nat} (hg : canonK 24 5 (mask 5) (24 * 5) g = true)
    (hgi : canonK 24 5 (mask 5) (24 * 5) gi = true)
    (hi : invEqK 24 5 (mask 5) (24 * 5) g gi = true)
    (hx : canonK 24 5 (mask 5) (24 * 5) x = true) (hy : canonK 24 5 (mask 5) (24 * 5) y = true) :
    tblEq 24 (conjT 24 (tabT (unpack 24 5 g)) (invT 24 (tabT (unpack 24 5 g)))
      (tabT (unpack 24 5 x))) (tabT (unpack 24 5 y)) = Nat.beq (pc (pc g x) gi) y := by
  rw [invT_unpack (by norm_num) hi, conjT_unpack hg hgi hx,
    tblEq_unpack (canonK_pcomp (canonK_pcomp hg hx) hgi) hy]
  rfl

theorem conjI_unpack {g gi x xi : Nat} (hg : canonK 24 5 (mask 5) (24 * 5) g = true)
    (hgi : canonK 24 5 (mask 5) (24 * 5) gi = true)
    (hi : invEqK 24 5 (mask 5) (24 * 5) g gi = true)
    (hx : canonK 24 5 (mask 5) (24 * 5) x = true) (hxi : canonK 24 5 (mask 5) (24 * 5) xi = true)
    (hxe : invEqK 24 5 (mask 5) (24 * 5) x xi = true) :
    tblEq 24 (conjT 24 (tabT (unpack 24 5 g)) (invT 24 (tabT (unpack 24 5 g)))
      (tabT (unpack 24 5 x))) (invT 24 (tabT (unpack 24 5 x))) = Nat.beq (pc (pc g x) gi) xi := by
  rw [invT_unpack (by norm_num) hxe]
  exact conj_unpack hg hgi hi hx hxi

theorem m12_ok : m12DataOK = true := by
  obtain ⟨⟨ta, ca⟩, ⟨tb, cb⟩, ⟨ty, cy⟩, ⟨tx, cx⟩⟩ := m12_tabs
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := rels
  have ia := s_invs 0 (by norm_num)
  have ib := s_invs 1 (by norm_num)
  have iy := s_invs 2 (by norm_num)
  have ix := s_invs 3 (by norm_num)
  unfold m12DataOK
  rw [enum_ok, Bool.and_true]
  simp only [Bool.and_eq_true]
  rw [ta, tb, ty, tx, pow4_unpack ca, pow4_unpack cb, commTT_unpack ca cb, sq_unpack cy,
    sq_unpack cx, commTT_unpack cy cx, conj_unpack cy iy.2 iy.1 ca cb,
    conj_unpack cy iy.2 iy.1 cb ca, conjI_unpack cx ix.2 ix.1 ca ia.2 ia.1,
    conjI_unpack cx ix.2 ix.1 cb ib.2 ib.1]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩, r8⟩, r9⟩, r10⟩

end CertificateChecks.KernelSpor.M12Syl

end
