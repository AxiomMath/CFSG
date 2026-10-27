module

public import Certificates.Kernel.HS3850.Cover
public import Certificates.Kernel.HS3850.FoursFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126
open CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HypOne
open CFSG.EvenSporadicStandard.TwoHS CertificateChecks.KernelSporSch CFSG.Sporadic.Schreier.Native
open CFSG.KD.LQT.HO (Cn cIdn)
open CFSG.KD.LQT.HN (ls8)
open CFSG.Sporadic.Schreier (hsStrongArrs)
open CFSG.KS.PF (strictN_eqP)

theorem wordT_size' (gens : Int → Table) : ∀ wd, (wordT 3850 gens wd).size = 3850
  | [] => by simp [wordT, idT]
  | l :: wd => by
    have e : wordT 3850 gens (l :: wd) = (wordT 3850 gens wd).map (fun t => (gens l)[t.toNat]!) :=
      rfl
    rw [e, Array.size_map, wordT_size' gens wd]

theorem map_compT {P T : Table} (hT : T.size = 3850) :
    T.map (fun t => P[t.toNat]!) = compT 3850 P T := by
  apply Array.ext (by simp [compT, hT])
  intro i h1 h2
  simp only [Array.getElem_map, compT, Array.getElem_ofFn]
  rw [getElem!_pos T i (by simpa using h1)]

theorem sCn {j : Nat} (hj : j < 2) : Cn (PHSC.S j) := by
  have h := allN_spec CertificateChecks.KernelSporSch.PHSCheck.canonOK j hj
  exact ((bAnd_iff _ _).1 h).1

private theorem tab2_get0 (a b : Table) : (#[a, b] : Array Table)[0]! = a := rfl
private theorem tab2_get1 (a b : Table) : (#[a, b] : Array Table)[1]! = b := rfl
private theorem map_tabT (a : Array Nat) : a.map UInt32.ofNat = tabT a := rfl

theorem gen_tab {l : Int} (hl : l = 0 ∨ l = 1) :
    coverGen l = tabT (unpack 3850 12 (ls8 l.toNat)) ∧ Cn (ls8 l.toNat) := by
  have hl2 : l.toNat < 2 := by rcases hl with rfl | rfl <;> decide
  have hs : ls8 l.toNat = PHSC.S l.toNat := by
    unfold ls8 letterK
    rw [CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.blt_dec]
    simp only [show l.toNat < 8 by omega, decide_true, ↓reduceIte]
  rw [hs]
  refine ⟨?_, sCn hl2⟩
  have e : coverGen l = hsStrongArrs[l.toNat]!.map UInt32.ofNat := by
    rw [coverGen.eq_1, hsPGTbls.eq_1]
    rcases hl with rfl | rfl
    · rw [show (0 : Int).toNat = 0 from rfl, tab2_get0]
    · rw [show (1 : Int).toNat = 1 from rfl, tab2_get1]
  rw [e, CertificateChecks.KernelSporSch.PHSCheck.arr_eq _ (by omega), map_tabT]

theorem wordT_ls8 : ∀ (wd : List Int), (∀ l ∈ wd, l = 0 ∨ l = 1) →
    wordT 3850 coverGen wd = tabT (unpack 3850 12 (wfoldR ls8 (wd.map Int.toNat))) ∧
      Cn (wfoldR ls8 (wd.map Int.toNat))
  | [], _ => ⟨hid, hidc⟩
  | l :: wd, h => by
    obtain ⟨ih, cih⟩ := wordT_ls8 wd fun l' hl' => h l' (List.mem_cons_of_mem l hl')
    obtain ⟨hg, cg⟩ := gen_tab (h l List.mem_cons_self)
    have e : wordT 3850 coverGen (l :: wd) =
        (wordT 3850 coverGen wd).map (fun t => (coverGen l)[t.toNat]!) := rfl
    have ew : wfoldR ls8 ((l :: wd).map Int.toNat) =
        pc (ls8 l.toNat) (wfoldR ls8 (wd.map Int.toNat)) := by
      rw [List.map_cons]
      exact strictN_eqP _ _
    rw [e, map_compT (wordT_size' _ _), ih, hg, compT_pc cg cih, ew]
    exact ⟨rfl, cn_pc cg cih⟩

theorem a_parts : Cn cvX ∧ Cn cvN ∧ Cn cvNI ∧
    invEqK 3850 12 (mask 12) (3850 * 12) cvN cvNI = true ∧ Nat.beq cvX idn = false ∧
    Nat.beq (pc cvX cvX) idn = true ∧ Nat.beq (pc cvX cvX2) (pc cvX2 cvX) = true ∧
    Nat.beq (pc cvX cvX3) (pc cvX3 cvX) = true ∧
    Nat.beq (pc (pc cvN cvX3) cvNI) (pc cvX cvX2) = true := by
  have h := ok25552a
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, h6, h7, h8, h9⟩
  revert h5
  cases Nat.beq cvX idn <;> simp

theorem x_tab : coverX = tabT (unpack 3850 12 cvX) := (wordT_ls8 _ (by decide)).1

theorem n_tab : coverN = tabT (unpack 3850 12 cvN) := (wordT_ls8 _ (by decide)).1

theorem ni_tab : coverNInv = tabT (unpack 3850 12 cvNI) := by
  unfold coverNInv
  rw [n_tab, invT_unpack (by norm_num) a_parts.2.2.2.1]

theorem x2_tab : coverX2 = tabT (unpack 3850 12 cvX2) := by
  obtain ⟨cX, cN, cNI, -⟩ := a_parts
  unfold coverX2 conjT
  rw [n_tab, ni_tab, x_tab, compT_pc cN cX, compT_pc (cn_pc cN cX) cNI]
  unfold cvX2
  rfl

theorem x3_tab : coverX3 = tabT (unpack 3850 12 cvX3) := by
  obtain ⟨cX, cN, cNI, -⟩ := a_parts
  have cX2 : Cn cvX2 := cn_pc (cn_pc cN cX) cNI
  unfold coverX3 conjT
  rw [n_tab, ni_tab, x2_tab, compT_pc cN cX2, compT_pc (cn_pc cN cX2) cNI]
  unfold cvX3
  rfl

theorem conj_tab {k : Nat} (hk : k < 2) : coverConjTbl k = tabT (unpack 3850 12 (CC.F k)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound CC.all (by norm_num) k hk
  rw [← CC.eq] at h
  rw [← tabT_natArr (coverConjTbl k)]
  exact congrArg tabT h

theorem cvK_spec {C L R : Nat} {w : List Nat} (h : cvK C L R w = true) :
    C = wfoldR ls8 w ∧ Cn C ∧ Cn (pinvS 3850 12 (mask 12) C) ∧
      invEqK 3850 12 (mask 12) (3850 * 12) C (pinvS 3850 12 (mask 12) C) = true ∧
      Nat.beq (pc (pc (pc L R) (pinvS 3850 12 (mask 12) L)) (pinvS 3850 12 (mask 12) R))
        (pc (pc C cvX) (pinvS 3850 12 (mask 12) C)) = true := by
  unfold cvK at h
  simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, h2, h3, h4, h5⟩

theorem sift_word {t : Table}
    {C : Nat} {w : List Nat} (hw : ∀ x ∈ w, x < 16) (ht : t = tabT (unpack 3850 12 C)) (cC : Cn C)
    (e : C = wfoldR ls8 w) : hsSift t = true := by
  obtain ⟨g, hg, hrep⟩ := CFSG.KD.LQT.HN.rep_word w hw
  rw [← e] at hrep
  rw [ht]
  refine (CFSG.KD.LQT.HN.sift_iff (G := g) ?_).2 hg
  rw [natArr_tabT cC]
  exact hrep

theorem mem_of {t : Table}
    {C : Nat} {w : List Nat} (hw : ∀ x ∈ w, x < 16) (ht : t = tabT (unpack 3850 12 C)) (cC : Cn C)
    (cCI : Cn (pinvS 3850 12 (mask 12) C))
    (iC : invEqK 3850 12 (mask 12) (3850 * 12) C (pinvS 3850 12 (mask 12) C) = true)
    (e : C = wfoldR ls8 w) : coverMemOK t = true := by
  have hs := sift_word hw ht cC e
  unfold coverMemOK coverPermOK
  rw [hs, ht, invT_unpack (by norm_num) iC, permOK_unpack cC iC, invOK_unpack cC cCI iC]
  rfl

theorem perm_of {t : Table} {C : Nat} (ht : t = tabT (unpack 3850 12 C)) (cC : Cn C)
    (cCI : Cn (pinvS 3850 12 (mask 12) C))
    (iC : invEqK 3850 12 (mask 12) (3850 * 12) C (pinvS 3850 12 (mask 12) C) = true) :
    coverPermOK t = true := by
  unfold coverPermOK
  rw [ht, invT_unpack (by norm_num) iC, permOK_unpack cC iC, invOK_unpack cC cCI iC]
  rfl

theorem conjEq_of {l c ρ : Table} {L C R : Nat} (hl : l = tabT (unpack 3850 12 L))
    (hc : c = tabT (unpack 3850 12 C)) (hr : ρ = tabT (unpack 3850 12 R)) (cL : Cn L)
    (cLI : Cn (pinvS 3850 12 (mask 12) L))
    (iL : invEqK 3850 12 (mask 12) (3850 * 12) L (pinvS 3850 12 (mask 12) L) = true)
    (cR : Cn R) (cRI : Cn (pinvS 3850 12 (mask 12) R))
    (iR : invEqK 3850 12 (mask 12) (3850 * 12) R (pinvS 3850 12 (mask 12) R) = true)
    (cC : Cn C) (cCI : Cn (pinvS 3850 12 (mask 12) C))
    (iC : invEqK 3850 12 (mask 12) (3850 * 12) C (pinvS 3850 12 (mask 12) C) = true)
    (h : Nat.beq (pc (pc (pc L R) (pinvS 3850 12 (mask 12) L)) (pinvS 3850 12 (mask 12) R))
        (pc (pc C cvX) (pinvS 3850 12 (mask 12) C)) = true) :
    coverConjEqOK l c ρ = true := by
  have cX := a_parts.1
  unfold coverConjEqOK commTable conjT
  rw [hl, hc, hr, x_tab, invT_unpack (by norm_num) iL, invT_unpack (by norm_num) iR,
    invT_unpack (by norm_num) iC, compT_pc cL cR, compT_pc (cn_pc cL cR) cLI,
    compT_pc (cn_pc (cn_pc cL cR) cLI) cRI, compT_pc cC cX, compT_pc (cn_pc cC cX) cCI,
    tblEq_unpack (cn_pc (cn_pc (cn_pc cL cR) cLI) cRI) (cn_pc (cn_pc cC cX) cCI)]
  exact h

theorem b_of {k r : Nat}
    (hk : k < 2) (hr : r < 43) (hfw : ∀ x ∈ (if k = 0 then fw0 else fw1), x < 16)
    (hcw : ∀ x ∈ cvW k, x < 16)
    (h4 : fourK (FG.F k) (HC.F r) (if k = 0 then fw0 else fw1) = true)
    (h5 : cvK (CC.F k) (FG.F k) (HC.F r) (cvW k) = true) :
    coverMemOK (foursTbl k) = true ∧ coverMemOK (coverConjTbl k) = true ∧
      coverPermOK (hsCentTbl r) = true ∧
      coverConjEqOK (foursTbl k) (coverConjTbl k) (hsCentTbl r) = true := by
  obtain ⟨e, cL, cLI, iL, cR, cRI, iR, -⟩ := fourK_spec h4
  obtain ⟨eC, cC, cCI, iC, hq⟩ := cvK_spec h5
  exact ⟨mem_of hfw (fours_tab hk) cL cLI iL e, mem_of hcw (conj_tab hk) cC cCI iC eC,
    perm_of (cent_tab hr) cR cRI iR,
    conjEq_of (fours_tab hk) (conj_tab hk) (cent_tab hr) cL cLI iL cR cRI iR cC cCI iC hq⟩

open Certificates in
open CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HSStd in
theorem facts25552 :
    (coverNInvOK = true ∧ coverXNeOK = true ∧ coverXSqOK = true ∧ coverComm2OK = true ∧
      coverComm3OK = true ∧ coverConj3OK = true) ∧
    (coverMemOK (foursTbl 0) = true ∧ coverMemOK (coverConjTbl 0) = true ∧
      coverPermOK rho2 = true ∧ coverConjEqOK (foursTbl 0) (coverConjTbl 0) rho2 = true) ∧
    (coverMemOK (foursTbl 1) = true ∧ coverMemOK (coverConjTbl 1) = true ∧
      coverPermOK rho3 = true ∧ coverConjEqOK (foursTbl 1) (coverConjTbl 1) rho3 = true) := by
  obtain ⟨cX, cN, cNI, iN, f1, f2, f3, f4, f5⟩ := a_parts
  have cX2 : Cn cvX2 := cn_pc (cn_pc cN cX) cNI
  have cX3 : Cn cvX3 := cn_pc (cn_pc cN cX2) cNI
  obtain ⟨g0, g1⟩ := (by simpa only [bAnd_iff] using ok25370 :
    fourK (FG.F 0) (HC.F 21) fw0 = true ∧ fourK (FG.F 1) (HC.F 34) fw1 = true)
  obtain ⟨c0, c1⟩ := (by simpa only [bAnd_iff] using ok25552b :
    cvK (CC.F 0) (FG.F 0) (HC.F 21) (cvW 0) = true ∧ cvK (CC.F 1) (FG.F 1) (HC.F 34) (cvW 1) = true)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, b_of (k := 0) (r := 21) (by norm_num) (by norm_num) (by decide)
    (by decide) g0 c0, b_of (k := 1) (r := 34) (by norm_num) (by norm_num) (by decide) (by decide)
    g1 c1⟩
  · unfold coverNInvOK
    rw [n_tab, ni_tab]
    exact invOK_unpack cN cNI iN
  · unfold coverXNeOK
    rw [x_tab, hid, tblEq_unpack cX hidc]
    change (!Nat.beq cvX idn) = true
    rw [f1]
    rfl
  · unfold coverXSqOK
    rw [x_tab, compT_pc cX cX, hid, tblEq_unpack (cn_pc cX cX) hidc]
    exact f2
  · unfold coverComm2OK commTT
    rw [x_tab, x2_tab, compT_pc cX cX2, compT_pc cX2 cX, tblEq_unpack (cn_pc cX cX2) (cn_pc cX2 cX)]
    exact f3
  · unfold coverComm3OK commTT
    rw [x_tab, x3_tab, compT_pc cX cX3, compT_pc cX3 cX, tblEq_unpack (cn_pc cX cX3) (cn_pc cX3 cX)]
    exact f4
  · unfold coverConj3OK conjT
    rw [n_tab, ni_tab, x_tab, x2_tab, x3_tab, compT_pc cN cX3, compT_pc (cn_pc cN cX3) cNI,
      compT_pc cX cX2, tblEq_unpack (cn_pc (cn_pc cN cX3) cNI) (cn_pc cX cX2)]
    exact f5

end CFSG.KD.HS3850

end
