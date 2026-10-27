module

public import Certificates.Kernel.Sporadic.McLC.Bool
public import Certificates.Kernel.Sporadic.McLC.SylK
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.BfsPinAlg

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

section Lemmas

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.SmallOddCore CFSG.ClassicalInvolution
open CFSG.KS.SporSch CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3.Native CFSG.KS.Raw CFSG.Sporadic.SmallOddCore.Native
open CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin

theorem tbl_ext {T U : Table} (hT : T.size = 275) (hU : U.size = 275)
    (h : ∀ x < 275, ap T x = ap U x) : T = U := by
  apply Array.ext (by rw [hT, hU])
  intro i h1 h2
  have e := h i (by omega)
  unfold ap at e
  rw [getElem!_pos T i h1, getElem!_pos U i h2] at e
  exact UInt32.toNat_inj.1 e

theorem compT_size (P Q : Table) : (compT 275 P Q).size = 275 := by simp [compT]

theorem wordTbl_size (gs : List Table) (w : List Nat) : (wordTbl 275 gs w).size = 275 := by
  unfold wordTbl
  suffices h : ∀ (w : List Nat) (acc : Table), acc.size = 275 →
      (w.foldl (fun acc l => compT 275 acc (gs.getD (l - 1) (idT 275))) acc).size = 275 from
    h w _ (by simp [idT])
  intro w
  induction w with
  | nil => exact fun _ h => h
  | cons l w ih =>
    intro acc _
    rw [List.foldl_cons]
    exact ih _ (compT_size _ _)

theorem tabT_size (p : Nat) : (tabT (unpack 275 9 p)).size = 275 := by
  unfold tabT
  rw [Array.size_map, CFSG.KS.PEnum.unpack_size]

theorem ap_unpack {p : Nat} (hp : cKS p = true) {x : Nat} (hx : x < 275) :
    ap (tabT (unpack 275 9 p)) x = pk p x := by
  rw [ap_tabT _ (unpack_lt hp), CFSG.KS.Raw.Orb.unpack_get hx]
  rfl

theorem ap_compT' {P Q : Table} {i : Nat} (hi : i < 275) :
    ap (compT 275 P Q) i = ap P (ap Q i) := by
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem ap_idT' {i : Nat} (hi : i < 275) : ap (idT 275) i = i := by
  unfold ap idT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem invoOK_eq (P : Table) :
    CFSG.Sporadic.Th.Native.invoOK 275 P = tblEq 275 (compT 275 P P) (idT 275) := by
  apply Bool.eq_iff_iff.2
  rw [CFSG.Sporadic.Schreier.tblEq_iff]
  unfold CFSG.Sporadic.Th.Native.invoOK
  rw [allIn_eq_true]
  constructor
  · intro h i hi
    rw [ap_compT' hi, ap_idT' hi]
    exact beq_iff_eq.1 (h i (Nat.zero_le _) hi)
  · intro h i _ hi
    rw [beq_iff_eq, ← ap_compT' hi, h i hi, ap_idT' hi]

theorem sylBase : szOK 275 9 = true ∧ cKS (pidn 275 9) = true ∧
    CFSG.KS.Prim.idK 275 9 (mask 9) = true ∧
    allN 4 (fun j => bAnd(cKS (McLCS.GI j), bAnd(Nat.beq (McLCS.G j) (pidn 275 9),
      bAnd(cKS (McLCSI j), invEqK 275 9 (mask 9) (275 * 9) (McLCS.GI j) (McLCSI j))))) = true ∧
    McLCS.cnt = 128 ∧ penumHdK (pidn 275 9) McLCS.cnt 50000 McLCS.T McLCS.PL = true := by
  have h := sylBase_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨a1, a2, a3, a4, Nat.eq_of_beq_eq_true a5, a6⟩

theorem sylGen {j : Nat} (hj : j < 4) : cKS (McLCS.GI j) = true ∧ McLCS.G j = pidn 275 9 ∧
    cKS (McLCSI j) = true ∧ invEqK 275 9 (mask 9) (275 * 9) (McLCS.GI j) (McLCSI j) = true := by
  have h := allN_spec sylBase.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4⟩ := h
  exact ⟨a1, Nat.eq_of_beq_eq_true a2, a3, a4⟩

theorem hid : idT 275 = tabT (unpack 275 9 (pidn 275 9)) := by
  rw [idT_tabT, CFSG.KC.BfsPin.idA_eq sylBase.1]

theorem involOK_unpack {p : Nat} (hp : cKS p = true) :
    involOK 275 (tabT (unpack 275 9 p)) =
      (Nat.beq (pcomp 275 9 (mask 9) p p) (pidn 275 9) && !Nat.beq p (pidn 275 9)) := by
  unfold involOK
  rw [invoOK_eq, compT_unpack hp hp, hid, tblEq_unpack (canonK_pcomp hp hp) sylBase.2.1,
    tblEq_unpack hp sylBase.2.1]

theorem sgens_get {j : Nat} (hj : j < 4) :
    McLData.sgens.toArray[j]! = wordTbl 275 McLData.kgens (McLData.sWords.getD j []) := by
  have hl : j < McLData.sWords.length := by simp [McLData.sWords]; omega
  unfold McLData.sgens
  rw [getElem!_pos _ j (by simpa using hl)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem _ _ hl]

theorem sWords_get {j : Nat} (hj : j < 4) : ∀ l ∈ McLData.sWords.getD j [], l = 1 ∨ l = 2 := by
  have hl : j < McLData.sWords.length := by simp [McLData.sWords]; omega
  rw [List.getD_eq_getElem _ _ hl]
  exact sWords_letters _ (List.getElem_mem hl)

theorem sylGen_spec {j : Nat} (hj : j < 4) {x : Nat} (hx : x < 275) :
    pk (McLCS.GI j) x = List.foldr GK x (McLData.sWords.getD j []) :=
  Nat.eq_of_beq_eq_true (allN_spec (allN_spec sylGen_ok j hj) x hx)

theorem s_tabs : TabsOK 275 9 4 McLCS.GI McLData.sgens.toArray := by
  refine ⟨by simp [McLData.sgens, McLData.sWords], fun j hj => ⟨?_, (sylGen hj).1⟩⟩
  rw [sgens_get hj]
  apply tbl_ext (wordTbl_size _ _) (tabT_size _)
  intro x hx
  rw [ap_unpack (sylGen hj).1 hx, sylGen_spec hj hx, rep_word_kgens (sWords_get hj) x hx,
    idx_eq, foldr_wp (fun c _ y hy => GK_eq c hy) hx]

theorem s_invs : ∀ j < 4, invEqK 275 9 (mask 9) (275 * 9) (McLCS.GI j) (McLCSI j) = true ∧
    canonK 275 9 (mask 9) (275 * 9) (McLCSI j) = true := fun j hj =>
  ⟨(sylGen hj).2.2.2, (sylGen hj).2.2.1⟩

theorem s_pe : ∀ i < McLCS.cnt, penumPtK 275 9 (mask 9) (275 * 9) true McLCS.G McLCS.GI 4
    McLCS.cnt McLCS.T McLCS.PL McLCS.POS McLCS.SRT McLCS.SRI i = true :=
  fun i hi => penumSl_spec sylE_ok i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < McLCS.cnt,
    hsortPtK 275 9 (mask 9) McLCS.cnt McLCS.T McLCS.HS McLCS.HSI i = true :=
  fun i hi => slK_spec sylH_ok i (Nat.zero_le _) (by omega) hi

theorem s_cl : ∀ c < McLCS.cnt * (4 + 4), findPtK McLCS.cnt McLCS.T
    (prodQK 275 9 (mask 9) (4 + 4) McLCS.T (bothK 4 McLCS.GI McLCSI)) McLCSCl c = true :=
  fun c hc => slK_spec sylCl_ok c (Nat.zero_le _) (by change c < Nat.mul McLCS.cnt 8; omega)
    (by change c < Nat.mul McLCS.cnt 8; omega)

theorem s_canon : ∀ i < McLCS.cnt, cKS (McLCS.T i) = true :=
  fun i hi => penumPt_canon (s_pe i hi)

theorem closure_eq :
    mulClosureH 275 McLData.sgens.toArray McLProof.capK = hRec 275 9 McLCS.cnt McLCS.T McLCS.PL ∧
    mulTreeOK 275 McLData.sgens.toArray (hRec 275 9 McLCS.cnt McLCS.T McLCS.PL).1
      (hRec 275 9 McLCS.cnt McLCS.T McLCS.PL).2.1
      (hRec 275 9 McLCS.cnt McLCS.T McLCS.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 McLCS.cnt McLCS.T McLCS.PL).1.toList = true :=
  mulH_sound sylBase.1 (fun j hj => (sylGen hj).2.1) s_tabs sylBase.2.2.2.2.2 s_pe s_hs

theorem conjWords_get {j : Nat} (hj : j < 35) :
    ∀ l ∈ McLData.conjWords.getD j [], l = 1 ∨ l = 2 := by
  have hl : j < McLData.conjWords.length := by simp [McLData.conjWords]; omega
  rw [List.getD_eq_getElem _ _ hl]
  exact conjWords_letters _ (List.getElem_mem hl)

theorem conjTbls_eq : McLData.conjTbls = McLData.conjWords.map fun w =>
    conjT 275 (wordTbl 275 McLData.abT w) (invT 275 (wordTbl 275 McLData.abT w)) McLData.Ta :=
  rfl

theorem CJ_spec {j : Nat} (hj : j < 35) {y : Nat} (hy : y < 275) :
    pk (McLCSJ j) y = actN (wp qAB (McLData.conjWords.getD j []) * alP *
      (wp qAB (McLData.conjWords.getD j []))⁻¹) y := by
  have hw := conjWords_get hj
  have h := allN_spec sylConj_ok j hj
  rw [bAnd_iff] at h
  have hx := actN_lt (wp qAB (McLData.conjWords.getD j []))⁻¹ hy
  have e := Nat.eq_of_beq_eq_true (allN_spec h.2 _ hx)
  rw [foldr_wp (fun c hc z hz => GA_eq (hw c hc) hz) hx, ← actN_mul, mul_inv_cancel, actN_one,
    ← actN_alP hx, foldr_wp (fun c hc z hz => GA_eq (hw c hc) hz) (actN_lt _ hx)] at e
  rw [e, actN_mul, actN_mul]

theorem conj_mem {j : Nat} (hj : j < 35) : tabT (unpack 275 9 (McLCSJ j)) ∈ McLData.conjTbls := by
  have hl : j < McLData.conjWords.length := by simp [McLData.conjWords]; omega
  have hc := (bAnd_iff _ _).1 (allN_spec sylConj_ok j hj)
  rw [conjTbls_eq]
  refine List.mem_map.2 ⟨McLData.conjWords.getD j [],
    by rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl, ?_⟩
  apply tbl_ext (compT_size _ _) (tabT_size _)
  intro x hx
  rw [ap_unpack hc.1 hx, CJ_spec hj hx]
  exact ((rep_conj (rep_word_abT (conjWords_get hj)) rep_Ta) x hx).trans (idx_eq _ _)

theorem enum_ok : enumOK 275 McLProof.capK 128 McLData.sgens = true := by
  obtain ⟨e, ht, hd⟩ := closure_eq
  unfold enumOK
  simp only [Bool.and_eq_true]
  rw [e]
  refine ⟨⟨⟨⟨?_, ht⟩, closedOK_of s_canon (TabsOK_both s_tabs s_invs) s_cl⟩, hd⟩, ?_⟩
  · refine List.all_eq_true.2 fun g hg => ?_
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
    exact invOK_of_rep (rep_word_kgens (sWords_letters w hw))
  · rw [hRec_size, sylBase.2.2.2.2.1]
    exact beq_self_eq_true 128

theorem cover_ok : McLProof.sylowCoverOK = true := by
  unfold McLProof.sylowCoverOK
  rw [closure_eq.1]
  unfold hRec
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < McLCS.cnt := by simpa using hi
  simp only [Array.getElem_ofFn]
  rw [involOK_unpack (s_canon i hi')]
  have h := allN_spec sylCov_ok i (by rw [← sylBase.2.2.2.2.1]; exact hi')
  unfold covS at h
  rw [bIf_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rw [bIf_iff] at h2
    rcases h2 with ⟨h3, -⟩ | ⟨h3, h4⟩
    · rw [h1, h3]
      rfl
    · rw [h1, h3]
      obtain ⟨j, hj, e⟩ := List.any_eq_true.1 h4
      simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or]
      refine List.any_eq_true.2 ⟨_, conj_mem (List.mem_range.1 hj), ?_⟩
      rw [← Nat.eq_of_beq_eq_true e]
      exact tblEqH_self _ _
  · rw [h1]
    rfl

end Lemmas

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.McLProof
open CFSG.Sporadic.SmallOddCore hiding coverOK
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native
  CFSG.ClassicalInvolution.McLData

theorem sylow_ok : enumOK 275 capK 128 sgens = true ∧ sylowCoverOK = true := ⟨enum_ok, cover_ok⟩

end CertificateChecks.KernelSpor.McLC

end
