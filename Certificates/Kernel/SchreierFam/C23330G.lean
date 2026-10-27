module

public import Certificates.Kernel.SchreierFam.C23330O
public import Certificates.Kernel.LocalComp.HeFixBind
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSchreierFam.He23330

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.Sporadic.HeldB
  CFSG.ComponentClassification.SolMax.HeGen CertificateChecks.KernelLC.HeFix
  CertificateChecks.KernelSpor CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

noncomputable abbrev U (p : Nat) : Array Nat := unpack 8330 14 p

theorem ucomp {p q : Nat} (hp : cnK p = true) (hq : cnK q = true) :
    compA 8330 (U p) (U q) = U (pc p q) := by
  refine compEqK_sound ?_
  unfold compEqK
  rw [bAnd_iff, bAnd_iff]
  exact ⟨hp, hq, Nat.beq_refl _⟩

theorem ucn {p q : Nat} (hp : cnK p = true) (hq : cnK q = true) : cnK (pc p q) = true :=
  canonK_pcomp hp hq

theorem ueq {p q : Nat} (hp : cnK p = true) (hq : cnK q = true) :
    eqA 8330 (U p) (U q) = Nat.beq p q :=
  eqA_unpack hp hq

theorem invK_facts {p q : Nat} (h : invK p q = true) :
    permOK 8330 14 (mask 14) (8330 * 14) p q = true ∧
      permOK 8330 14 (mask 14) (8330 * 14) q p = true ∧ cnK p = true ∧ cnK q = true := by
  unfold invK at h
  simp only [bAnd_iff] at h
  exact h

theorem uinv {p q : Nat} (h : invK p q = true) : invCand 8330 (U p) = U q :=
  (invEqK_sound (invK_facts h).1).1

theorem upermChk {p q : Nat} (h : invK p q = true) : permChk 8330 (U p) = true := by
  obtain ⟨h1, h2, -, -⟩ := invK_facts h
  obtain ⟨e1, i1⟩ := invEqK_sound h1
  obtain ⟨-, i2⟩ := invEqK_sound h2
  unfold permChk
  rw [e1, i1, i2]
  rfl

theorem beq_nbeq (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

theorem bne_nbeq (a b : Nat) : (a != b) = !Nat.beq a b := by
  rw [bne, beq_nbeq]

theorem uget {p i : Nat} (hi : i < 8330) : (U p)[i]! = pg 14 (mask 14) p i :=
  CFSG.KC.Misc.PairCount.unpack_get hi

theorem kC_at {i : Nat} (hi : i < 2) :
    wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (WC i) (CW i) = true ∧
      invK (CW i) (CWI i) = true := by
  refine ⟨?_, allN_spec kCI i hi⟩
  match i, hi with
  | 0, _ => exact kC0
  | 1, _ => exact kC1

theorem kD_at {j : Nat} (hj : j < 3) :
    wordEqK 8330 14 (mask 14) (pidn 8330 14) CW CWI 2 (heDerivedV.getD j []) (DW j) = true ∧
      invK (DW j) (DWI j) = true := by
  refine ⟨?_, allN_spec kDI j hj⟩
  match j, hj with
  | 0, _ => exact kD0
  | 1, _ => exact kD1
  | 2, _ => exact kD2

theorem kS_at {k : Nat} (hk : k < 9) : invK (SG k) (pi (SG k)) = true ∧
    (!Nat.beq (pg 14 (mask 14) (SG k) 0) 0 || FP.all fun x => stabK (SG k) x) = true := by
  have h := allN_spec kS k hk
  simpa only [bAnd_iff] using h

theorem kF_facts : wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wF1 F1 = true ∧
    wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wF2 F2 = true ∧
    wordEqK 8330 14 (mask 14) (pidn 8330 14) DW DWI 3 wC CC = true ∧
    wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 wG0 G0 = true ∧
    invK G0 G0I = true ∧ cnK F1 = true ∧ cnK F2 = true ∧ cnK CC = true ∧
    cnK ID = true := by
  have h := kF
  simp only [bAnd_iff] at h
  exact h

theorem letters_S : heLetterArrs.size = 3 ∧ ∀ j < 3, heLetterArrs[j]! = U (LU j) := by
  refine ⟨by simp [heLetterArrs], fun j hj => ?_⟩
  rw [heLetterArrs, arr_get _ (by simpa using hj)]
  match j, hj with
  | 0, _ => simpa [LU_0] using heGen_eq (k := 0) (by decide)
  | 1, _ => simpa [LU_1] using heGen_eq (k := 1) (by decide)
  | 2, _ => simpa [LU_2] using heU_eq

theorem ab_S : heABArrs.size = 2 ∧ ∀ j < 2, heABArrs[j]! = U (L2 j) := by
  refine ⟨by simp [heABArrs], fun j hj => ?_⟩
  rw [heABArrs, arr_get _ (by simpa using hj)]
  match j, hj with
  | 0, _ => simpa [L2_0] using heGen_eq (k := 0) (by decide)
  | 1, _ => simpa [L2_1] using heGen_eq (k := 1) (by decide)

theorem pC : allN 2 (fun i => permOK 8330 14 (mask 14) (8330 * 14) (CW i) (CWI i)) = true :=
  CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => (invK_facts (kC_at hi).2).1

theorem pD : allN 3 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (DW j) (DWI j)) = true :=
  CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => (invK_facts (kD_at hj).2).1

theorem wc_eq {i : Nat} (hi : i < 2) :
    wordA 8330 heLetterArrs (rawInvs 8330 heLetterArrs) (WC i) = U (CW i) :=
  (wordEqK_sound letters_S kPLU (kC_at hi).1).1

theorem c_S : heCArrs.size = 2 ∧ ∀ j < 2, heCArrs[j]! = U (CW j) := by
  refine ⟨by rw [heCArrs]; simp only [List.size_toArray, List.length_cons, List.length_nil],
    fun j hj => ?_⟩
  rw [heCArrs, arr_get _ (by simp only [List.length_cons, List.length_nil]; omega)]
  match j, hj with
  | 0, _ =>
    rw [List.getElem_cons_zero]
    exact wc_eq (i := 0) (by decide)
  | 1, _ =>
    rw [List.getElem_cons_succ, List.getElem_cons_zero]
    exact wc_eq (i := 1) (by decide)

theorem heD_eq {j : Nat} (hj : j < 3) : heDArr j = U (DW j) :=
  (wordEqK_sound c_S pC (kD_at hj).1).1

theorem d_S : dArrs.size = 3 ∧ ∀ j < 3, dArrs[j]! = U (DW j) := by
  refine ⟨by rw [dArrs]; simp only [List.size_toArray, List.length_cons, List.length_nil],
    fun j hj => ?_⟩
  rw [dArrs, arr_get _ (by simp only [List.length_cons, List.length_nil]; omega)]
  match j, hj with
  | 0, _ =>
    rw [List.getElem_cons_zero]
    exact heD_eq (by decide)
  | 1, _ =>
    rw [List.getElem_cons_succ, List.getElem_cons_zero]
    exact heD_eq (by decide)
  | 2, _ =>
    rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_zero]
    exact heD_eq (by decide)

theorem f1_eq : f1A = U F1 := (wordEqK_sound d_S pD kF_facts.1).1

theorem f2_eq : f2A = U F2 := (wordEqK_sound d_S pD kF_facts.2.1).1

theorem c_eq : cA = U CC := (wordEqK_sound d_S pD kF_facts.2.2.1).1

theorem g0_eq : g0A = U G0 := (wordEqK_sound ab_S kPL2 kF_facts.2.2.2.1).1

theorem id_eq : idA 8330 = U ID := hidA

theorem sg_eq {k : Nat} (hk : k < 9) : heStrong k = U (SG k) := HeText.heStrong_eq hk

theorem cG0 : cnK G0 = true := (invK_facts kF_facts.2.2.2.2.1).2.2.1

theorem cG0I : cnK G0I = true := (invK_facts kF_facts.2.2.2.2.1).2.2.2

theorem cD {j : Nat} (hj : j < 3) : cnK (DW j) = true := (invK_facts (kD_at hj).2).2.2.1

theorem fP_eq : fP = FP.map U := by
  have hcj : ∀ x, cnK x = true → conjBy g0A (U x) = U (cj x) := fun x hx => by
    rw [conjBy, g0_eq, uinv kF_facts.2.2.2.2.1, ucomp hx cG0, ucomp cG0I (ucn hx cG0), cj]
  rw [fP, f1_eq, f2_eq, FP, ucomp kF_facts.2.2.2.2.2.1 kF_facts.2.2.2.2.2.2.1,
    hcj _ kF_facts.2.2.2.2.2.1, hcj _ kF_facts.2.2.2.2.2.2.1,
    hcj _ (ucn kF_facts.2.2.2.2.2.1 kF_facts.2.2.2.2.2.2.1)]
  rfl

theorem cFP : ∀ y ∈ FP, cnK y = true := by
  have h1 := kF_facts.2.2.2.2.2.1
  have h2 := kF_facts.2.2.2.2.2.2.1
  intro y hy
  simp only [FP, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · exact ucn cG0I (ucn h1 cG0)
  · exact ucn cG0I (ucn h2 cG0)
  · exact ucn cG0I (ucn (ucn h1 h2) cG0)

theorem stab_eq {k : Nat} (hk : k < 9) {x : Nat} (hx : cnK x = true) :
    stabOK (heStrong k) (U x) = stabK (SG k) x := by
  obtain ⟨-, -, hs, hsi⟩ := invK_facts (kS_at hk).1
  rw [stabOK, stabK, fP_eq, List.any_map, sg_eq hk, uinv (kS_at hk).1, ucomp hx hsi,
    ucomp hs (ucn hx hsi), Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  have hc := ucn hs (ucn hx hsi)
  constructor
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, by rwa [Function.comp_apply, ueq hc (cFP y hy)] at e⟩
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, by rwa [Function.comp_apply, ueq hc (cFP y hy)]⟩

theorem heGenOuter_23330 : heGenOuterCheck = true := by
  have h1 := kF_facts.2.2.2.2.2.1
  have h2 := kF_facts.2.2.2.2.2.2.1
  have h3 := kF_facts.2.2.2.2.2.2.2.1
  have hI := kF_facts.2.2.2.2.2.2.2.2
  have hperm : (List.range 3).all (fun j => permChk 8330 (heDArr j)) = true := by
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [heD_eq hj']
    exact upermChk (kD_at hj').2
  have hstrong : (List.range 9).all (fun k => permChk 8330 (heStrong k) &&
      ((heStrong k)[0]! != 0 || fP.all fun x => stabOK (heStrong k) x)) = true := by
    rw [List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    obtain ⟨hinv, hst⟩ := kS_at hk'
    have hall : (fP.all fun x => stabOK (heStrong k) x) = FP.all fun x => stabK (SG k) x := by
      rw [fP_eq, List.all_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      refine forall_congr' fun x => imp_congr_right fun hx => ?_
      rw [Function.comp_apply, stab_eq hk' (cFP x hx)]
    rw [Bool.and_eq_true, hall, sg_eq hk', uget (by decide), bne_nbeq]
    exact ⟨upermChk hinv, hst⟩
  have l1 : lettersOK 3 wF1 = true := by decide
  have l2 : lettersOK 3 wF2 = true := by decide
  have l3 : lettersOK 3 wC = true := by decide
  have l4 : lettersOK 2 wG0 = true := by decide
  have hg0 : permChk 8330 g0A = true := by
    rw [g0_eq]
    exact upermChk kF_facts.2.2.2.2.1
  have hD0 := cD (j := 0) (by decide)
  rw [heGenOuterCheck, hperm, hstrong, l1, l2, l3, l4, hg0, f1_eq, f2_eq, c_eq, g0_eq, id_eq,
    heD_eq (j := 0) (by decide), heD_eq (j := 2) (by decide), omega0, uget (by decide),
    uget (by decide), beq_nbeq, bne_nbeq,
    ucomp h1 h1, ucomp h2 h2, ucomp h1 h2, ucomp h2 h1, ucomp h3 h3, ucomp h3 (ucn h3 h3),
    ucomp h3 h1, ucomp h1 h3, ucomp h3 h2, ucomp h2 h3, ucomp h3 hD0, ucomp hD0 h3,
    ueq (ucn h1 h1) hI, ueq h1 hI, ueq (ucn h2 h2) hI, ueq h2 hI, ueq h1 h2,
    ueq (ucn h1 h2) (ucn h2 h1), ueq (ucn h3 (ucn h3 h3)) hI, ueq h3 hI,
    ueq (ucn h3 h1) (ucn h1 h3), ueq (ucn h3 h2) (ucn h2 h3), ueq (ucn h3 hD0) (ucn hD0 h3)]
  have e := kE
  simp only [Bool.true_and, Bool.and_true, Bool.and_assoc] at e ⊢
  exact e

end CertificateChecks.KernelSchreierFam.He23330
