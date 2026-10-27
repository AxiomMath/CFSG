
module

public import Certificates.Kernel.LocalComp.L34T1.Chk
public import Certificates.Kernel.LocalComp.L34Para.Final
public import Certificates.Kernel.LocalComp.L34ScanFinal
public import CFSG.Certificates.Kernel.L34Scan2Sound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsNoFrobCertInputs
public import Certificates.Data.SolMaxL34Graph
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34T1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan2 CFSG.KC.L34W CertificateChecks.KernelLC.L34X
open CertificateChecks.KernelLC.L34Cert CertificateChecks.KernelLC.L34Para
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

theorem sapp (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem hG : GensG L34R.G := fun j hj => ⟨bindR.2 j hj, cnG hj⟩

theorem htg (k : Nat) : Cn (tgP k) ∧ tgT k = unpack 42 6 (tgP k) := tgK_eq hG k

theorem nf_of {a : Bool} (h : notB a = false) : a = true := by
  cases a
  · exact absurd h (by decide)
  · rfl

theorem invOK_of {x xi : Nat} (cx : Cn x) (ci : Cn xi) (e : pcomp 42 6 (mask 6) x xi = pidn 42 6) :
    invOK (unpack 42 6 x) = true := by
  unfold invOK
  rw [invTab_eq_of_pcomp cx ci e, size_unpack, comp_inv_of_pcomp cx ci e, beq_self_eq_true,
    beq_self_eq_true]
  rfl

theorem borel_true : borelOK = true := by
  have hk := k22204
  unfold borelK at hk
  rw [sapp, sapp, sapp] at hk
  unfold borelOK
  dsimp only
  rw [rT.1, rB.1, size_pts, CFSG.KS.BfsReplay.allBelow_iff]
  intro i hi
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hk i hi
  rw [sapp] at h
  unfold borelPt at h
  have hx := rB.2.2.1 i hi
  rw [CFSG.KC.L34Scan.pts_get' hi]
  rcases orB_iff.1 h with h | h
  · rw [found_of_memL h]
    rfl
  · obtain ⟨a, h⟩ := andB_iff.1 h
    obtain ⟨b, c⟩ := andB_iff.1 h
    simp only [List.all_cons, List.all_nil, Bool.and_true, (htg 4).2, (htg 8).2, (htg 12).2,
      ncomm_of hx (htg 4).1 a, ncomm_of hx (htg 8).1 b, ncomm_of hx (htg 12).1 c, Bool.and_self,
      Bool.or_true]

theorem conj_pt {P : Nat → Nat} {k : Nat} {w : List Nat} (h : conjPt P (tgP 4) k w = true) :
    (found (indexOf (pts 42 6 960 P)) (pts 42 6 960 P) (wordTab w) && invOK (wordTab w) &&
      conjTab 42 (wordTab w) (invTab 42 (wordTab w)) (tgT k) == tgT 4) = true := by
  unfold conjPt at h
  rw [sapp, sapp] at h
  obtain ⟨hm, h⟩ := andB_iff.1 h
  obtain ⟨ci, h⟩ := andB_iff.1 h
  obtain ⟨hinv, hz⟩ := andB_iff.1 h
  obtain ⟨cx, ex⟩ := wordK_eq hG w
  have e := Nat.eq_of_beq_eq_true hinv
  obtain ⟨ck, ek⟩ := htg k
  obtain ⟨c4, e4⟩ := htg 4
  rw [ex, found_of_memL hm, invOK_of cx ci e, Bool.true_and, Bool.true_and]
  unfold conjTab
  rw [invTab_eq_of_pcomp cx ci e, ek, e4, comp_unpack' cx ck, comp_unpack' (canonK_pcomp cx ck) ci,
    beq_unpack (canonK_pcomp (canonK_pcomp cx ck) ci) c4]
  exact hz

theorem conj_true : conjOK = true := by
  have hk := k22205
  rw [sapp] at hk
  unfold conjK at hk
  obtain ⟨h1, h2⟩ := andB_iff.1 hk
  unfold conjOK
  dsimp only
  rw [r1.1, r2.1, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨fun d hd => conj_pt (List.all_eq_true.1 h1 d hd),
    fun d hd => conj_pt (List.all_eq_true.1 h2 d hd)⟩

theorem hx7 : Cn x7P ∧ x7T = unpack 42 6 x7P := by
  refine ⟨canonK_pcomp (cnG (by decide)) (cnG (by decide)), ?_⟩
  unfold x7T x7P
  rw [e1, e2, comp_unpack' (cnG (by decide)) (cnG (by decide))]

theorem hpow : ∀ k, Cn (ppowK x7P k) ∧ x7Pow x7T k = unpack 42 6 (ppowK x7P k) :=
  ppowK_spec hx7.1 (x7Pow x7T) rfl fun k => by
    rw [← hx7.2]
    rfl

theorem frob_true : noFrobOK = true := by
  have hk := k22214
  unfold frobK at hk
  rw [sapp, sapp] at hk
  obtain ⟨h7, h⟩ := andB_iff.1 hk
  obtain ⟨hne, hs⟩ := andB_iff.1 h
  unfold frobScan at hs
  unfold noFrobOK noFrobOrbit
  rw [hO0.1]
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [(hpow 7).2, idTab42, beq_unpack (hpow 7).1 cn_pidn]
    exact h7
  · rw [hx7.2, idTab42]
    exact nbeq_of hx7.1 cn_pidn hne
  · refine pts_all fun i hi => ?_
    have cu := pinO0.canon i hi
    have h := CFSG.KS.Raw.Orb.allN_iff.1 hs i hi
    rw [sapp] at h
    unfold frobPt at h
    rw [(hpow 6).2, hx7.2, comp_unpack' hx7.1 cu, comp_unpack' (canonK_pcomp hx7.1 cu) (hpow 6).1]
    exact ncomm_of cu (canonK_pcomp (canonK_pcomp hx7.1 cu) (hpow 6).1) h

theorem gu_true : CFSG.ComponentClassification.SolMax.L34Graph.l34GraphUnitaryCheck = true := by
  have hk := k23331
  unfold guK at hk
  rw [sapp] at hk
  have cr : Cn (RP 2) := cnRP (by decide)
  have cc := CertificateChecks.KernelLC.L34Scan.canonC.2.2
  unfold CFSG.ComponentClassification.SolMax.L34Graph.l34GraphUnitaryCheck
  dsimp only
  rw [hS.1, hO3.1, cent3, r3_eq]
  refine pts_toList_all fun i hi => ?_
  have cu := pinO3.canon i hi
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hk i hi
  rw [sapp] at h
  unfold guPt at h
  rw [Bool.or_eq_true]
  rcases orB_iff.1 h with h | h
  · exact Or.inl (ncomm_of cu cr h)
  · refine Or.inr (pts_toList_all fun a ha => pts_toList_any ?_)
    have h' := CFSG.KS.Raw.Orb.allN_iff.1 h a ha
    rw [sapp] at h'
    unfold guInner at h'
    obtain ⟨b, hb, hf⟩ := ex_of_notB_allN h'
    rw [sapp] at hf
    refine ⟨b, hb, ?_⟩
    have cs := cc a ha
    have cx := cc b hb
    rw [comp_unpack' cu cx, comp_unpack' (canonK_pcomp cu cx) cu,
      comp_unpack' (canonK_pcomp (canonK_pcomp cu cx) cu) cs, comp_unpack' cs cx,
      beq_unpack (canonK_pcomp (canonK_pcomp (canonK_pcomp cu cx) cu) cs) (canonK_pcomp cs cx), hf]
    rfl

theorem quat_true : quatOK = true := by
  have hk := k22202q
  rw [sapp, sapp, sapp] at hk
  unfold quatK at hk
  obtain ⟨h1, hk⟩ := andB_iff.1 hk
  obtain ⟨h2, hk⟩ := andB_iff.1 hk
  obtain ⟨h3, hk⟩ := andB_iff.1 hk
  obtain ⟨h4, hk⟩ := andB_iff.1 hk
  obtain ⟨h5, hk⟩ := andB_iff.1 hk
  obtain ⟨h6, hk⟩ := andB_iff.1 hk
  obtain ⟨h7, hk⟩ := andB_iff.1 hk
  obtain ⟨h8, h9⟩ := andB_iff.1 hk
  obtain ⟨ca, ea⟩ := htg 35
  obtain ⟨cb, eb⟩ := htg 38
  obtain ⟨cc, ec⟩ := htg 4
  unfold quatOK
  rw [ea, eb, ec, idTab42, comp_unpack' ca ca, comp_unpack' cb cb, comp_unpack' cc cc,
    comp_unpack' ca cb, comp_unpack' cb cc, comp_unpack' (canonK_pcomp cb cc) ca,
    comp_unpack' cc ca]
  rw [beq_unpack (canonK_pcomp ca ca) cc, beq_unpack (canonK_pcomp cb cb) cc,
    beq_unpack (canonK_pcomp cc cc) cn_pidn, beq_unpack cc cn_pidn,
    beq_unpack (canonK_pcomp ca cb) (canonK_pcomp (canonK_pcomp cb cc) ca), beq_unpack cb cn_pidn,
    beq_unpack cb ca, beq_unpack cb cc, beq_unpack cb (canonK_pcomp cc ca)]
  rw [h1, h2, h3, notB_iff.1 h4, h5, notB_iff.1 h6, notB_iff.1 h7, notB_iff.1 h8, notB_iff.1 h9]
  rfl

theorem sylWit_true : sylWitOK = true := by
  have hk := k22202s
  unfold sylK at hk
  rw [sapp] at hk
  have cr4 : Cn (RP 3) := cnRP (by decide)
  unfold sylWitOK
  dsimp only
  rw [rB.1, CFSG.KS.BfsReplay.allBelow_iff]
  intro k hkl
  have hk' : k < 105 := hkl
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hk k hk'
  have cy := canonY hk'
  obtain ⟨cyi, ey⟩ := andB_iff.1 (allN' kYI k hk')
  have hy : wordTab (wReps.getD k []) = unpack 42 6 (L34PR.Y k) := by
    rw [List.getD_eq_getElem _ _ hkl, ← wordTabs_getElem! wReps hkl]
    exact (gY.2 k hk').1
  have hyi : invTab 42 (wordTab (wReps.getD k [])) = unpack 42 6 (L34PR.YI k) := by
    rw [List.getD_eq_getElem _ _ hkl, ← wordTabs_getElem! wReps hkl,
      ← map_get (invTab 42) (by rw [gY.1]; exact hk')]
    exact invY.1 k hk'
  rw [Bool.or_eq_true]
  rcases orB_iff.1 h with h | h
  · left
    unfold notNormK at h
    rw [sapp] at h
    obtain ⟨i, hi, hf⟩ := ex_of_notB_allN h
    have hni := nf_of hf
    unfold r4NotNormalizes r4Conj
    dsimp only
    unfold conjTab
    rw [rT.1, hyi, hy, r4_eq, comp_unpack' cyi cr4, comp_unpack' (canonK_pcomp cyi cr4) cy,
      rT.2.2.2.1, anyBelow_iff]
    have cz := canonK_pcomp (canonK_pcomp cyi cr4) cy
    obtain ⟨ti, cti⟩ := rT.2.2.2.2 i hi
    refine ⟨i, hi, ?_⟩
    rw [ti, comp_unpack' cz cti, comp_unpack' (canonK_pcomp cz cti) cz]
    exact notIn_sound rfl (canonK_pcomp (canonK_pcomp cz cti) cz) rT.2.2.1 hni
  · right
    obtain ⟨e, he, hf⟩ := List.any_eq_true.1 h
    refine List.any_eq_true.2 ⟨e, he, ?_⟩
    obtain ⟨h1, h2⟩ := andB_iff.1 hf
    unfold witPt at h2
    rw [sapp, sapp] at h2
    obtain ⟨hcomm, h2⟩ := andB_iff.1 h2
    obtain ⟨ci, h2⟩ := andB_iff.1 h2
    obtain ⟨hinv, hm⟩ := andB_iff.1 h2
    have einv := Nat.eq_of_beq_eq_true hinv
    obtain ⟨cc, ec⟩ := wordK_eq hG e.2
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Nat.eq_of_beq_eq_true h1]
      exact beq_self_eq_true k
    · rw [ec, r4_eq]
      exact beq_iff_eq.2 ((commPt_iff cc cr4).1 hcomm)
    · rw [ec]
      exact invOK_of cc ci einv
    · rw [ec, invTab_eq_of_pcomp cc ci einv, hy, comp_unpack' ci cy]
      exact found_of_memL hm

theorem local_true : localOK = true := by
  unfold localOK
  rw [quat_true, sylWit_true]
  rfl

end CertificateChecks.KernelLC.L34T1

end
