module

public import Certificates.Kernel.GH74.J2CentH
public import Certificates.Kernel.GH74.EvSound
public import Certificates.Kernel.GH74.J2EvF

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2CentE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.GH74.Generic.S45.EvSpor CertificateChecks.KernelGH74
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn

theorem efacts : (∀ j < 4, involK (J2E.GI j) = true ∧ bIf(Nat.beq (J2E.GI j) tK, false, true) = true) ∧
    (∀ c < 17, r32 J2EP c < J2E.cnt ∧ J2E.T (r32 J2EP c) = ePQ c) ∧
    (∀ i < 32, cK (J2EAI i) = true ∧ iK (J2E.T i) (J2EAI i) = true) := by
  have h := e_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3⟩ := h
  refine ⟨fun j hj => ?_, fun c hc => ?_, fun i hi => ?_⟩
  · have := allN_spec a1 j hj
    simp only [bAnd_iff] at this
    exact this
  · have := allN_spec a2 c hc
    unfold atK at this
    simp only [bAnd_iff] at this
    exact ⟨Nat.le_of_ble_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩
  · have := allN_spec a3 i hi
    simp only [bAnd_iff] at this
    exact this

theorem e_mem {c : Nat} (hc : c < 17) : memT 315 j2E (tabT (unpack 315 9 (ePQ c))) = true := by
  obtain ⟨h1, h2⟩ := efacts.2.1 c hc
  rw [e_arr, ← h2]
  exact memT_of h1 (tblEq_self (eT h1))

theorem eGens_all {f : Table → Bool} :
    j2EGens.all f = true ↔ ∀ j < 4, f (tabT (unpack 315 9 (J2E.GI j))) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    have hm : j2EGens.toArray[j]! ∈ j2EGens := by
      rw [getElem!_pos _ j (by change j < 4; exact hj)]
      simp only [List.getElem_toArray]
      exact List.getElem_mem _
    rw [(e_tabs.2 j hj).1] at hm
    exact h _ hm
  · intro h x hx
    obtain ⟨j, hj, rfl, -⟩ := TabsOK_list e_tabs hx
    exact h j hj

theorem eEnum_ok : j2EEnumOK = true := by
  have hinv : invsOK 315 j2E = true := invsOK_of_enumOK (by norm_num) e_enum
  have htA : memT 315 j2E j2TA = true := by
    rw [tA_tab]
    exact e_mem (c := 0) (by norm_num)
  have hg : (j2EGens.all fun x => involOK 315 x && !tblEq 315 x j2TA) = true := by
    rw [eGens_all]
    intro j hj
    obtain ⟨h1, h2⟩ := efacts.1 j hj
    rw [involF (eg_canon hj), tA_tab, tblEq_unpack (eg_canon hj) tK_canon, h1, ← bIf_not' , h2]
    rfl
  unfold j2EEnumOK
  rw [e_enum, hinv, htA, hg]
  rfl

theorem eNormal_ok : j2ENormalOK = true := by
  unfold j2ENormalOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 4 := hi
  rw [← getElem!_pos j2CG i hi, cg_get hi', eGens_all]
  intro j hj
  rw [invF (by omega), tabF (by omega), conjT_unpack (Fc (by omega)) (Ic (by omega)) (eg_canon hj)]
  have e : pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) (F (32 + i)) (J2E.GI j)) (I (32 + i)) =
      ePQ (1 + 4 * i + j) := by
    interval_cases i <;> interval_cases j <;> rfl
  rw [e]
  exact e_mem (by omega)

theorem sf : ∀ i < 32, (bOr (Nat.beq (pc (J2E.T i) (J2E.T i)) idK) (Nat.beq (pc (J2E.T i) (J2E.T i)) tK)
    = true) ∧ ∀ j < 32, bOr (Nat.beq (cmK (J2E.T i) (J2E.T j) (J2EAI i) (J2EAI j)) idK)
      (Nat.beq (cmK (J2E.T i) (J2E.T j) (J2EAI i) (J2EAI j)) tK) = true := by
  intro i hi
  have h := allN_spec struct_ok i hi
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨h1, fun j hj => ?_⟩
  have := allN_spec h2 j hj
  rwa [CFSG.KS.GH74.strictB_eq] at this

theorem eAI_tab {i : Nat} (hi : i < 32) :
    invT 315 (tabT (unpack 315 9 (J2E.T i))) = tabT (unpack 315 9 (J2EAI i)) :=
  invT_unpack (by norm_num) (efacts.2.2 i hi).2

theorem e_cnt : J2E.cnt = 32 := sizes.1

theorem eT32 {i : Nat} (hi : i < 32) : canonK 315 9 (mask 9) (315 * 9) (J2E.T i) = true :=
  eT (by rw [e_cnt]; exact hi)

theorem eStruct_ok : j2EStructOK = true := by
  have hc : ∀ i < J2E.cnt, ∀ j < J2E.cnt,
      commutatorT 315 (tabT (unpack 315 9 (J2E.T i))) (tabT (unpack 315 9 (J2E.T j))) =
        tabT (unpack 315 9 (cmK (J2E.T i) (J2E.T j) (J2EAI i) (J2EAI j))) := by
    intro i hi j hj
    rw [e_cnt] at hi hj
    unfold commutatorT cmK pc
    rw [eAI_tab hi, eAI_tab hj, compT_unpack (eT32 hi) (eT32 hj),
      compT_unpack (efacts.2.2 i hi).1 (efacts.2.2 j hj).1,
      compT_unpack (CFSG.KC.BfsPin.canonK_pcomp (eT32 hi) (eT32 hj))
        (CFSG.KC.BfsPin.canonK_pcomp (efacts.2.2 i hi).1 (efacts.2.2 j hj).1)]
  have hcc : ∀ i < J2E.cnt, ∀ j < J2E.cnt,
      canonK 315 9 (mask 9) (315 * 9) (cmK (J2E.T i) (J2E.T j) (J2EAI i) (J2EAI j)) = true := by
    intro i hi j hj
    rw [e_cnt] at hi hj
    exact CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp (eT32 hi) (eT32 hj))
      (CFSG.KC.BfsPin.canonK_pcomp (efacts.2.2 i hi).1 (efacts.2.2 j hj).1)
  obtain ⟨cz, ct, ci⟩ := (show _ ∧ _ ∧ _ from by
    have h := center_ok
    simp only [bAnd_iff] at h
    exact h)
  have hall : ∀ i < J2E.cnt, ((hRec 315 9 J2E.cnt J2E.T J2E.PL).1.all fun y =>
      CFSG.Sporadic.SmallOddCore.commTT 315 (tabT (unpack 315 9 (J2E.T i))) y) =
      allN 32 (fun j => pcommK 315 9 (J2E.T i) (J2E.T j)) := by
    intro i hi
    apply Bool.eq_iff_iff.2
    rw [all_hRec_iff, CFSG.KS.PEnum.allN_iff _ _, e_cnt]
    refine forall₂_congr fun j hj => ?_
    rw [commF (eT hi) (eT (by rw [e_cnt]; exact hj)), pcommK_eq (eT hi) (eT (by rw [e_cnt]; exact hj))]
    rfl
  unfold j2EStructOK
  rw [e_arr]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [all_hRec_iff]
    intro i hi
    have hi' : i < 32 := by rw [e_cnt] at hi; exact hi
    obtain ⟨h1, h2⟩ := sf i hi'
    rw [Bool.and_eq_true, compT_unpack (eT hi) (eT hi), hid, tA_tab,
      tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp (eT hi) (eT hi)) hidc,
      tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp (eT hi) (eT hi)) tK_canon, all_hRec_iff]
    refine ⟨by rw [← bOr_eq]; exact h1, fun j hj => ?_⟩
    rw [hc i hi j hj, tblEq_unpack (hcc i hi j hj) hidc, tblEq_unpack (hcc i hi j hj) tK_canon,
      ← bOr_eq]
    exact h2 j (by rw [e_cnt] at hj; exact hj)
  · rw [all_hRec_iff]
    intro i hi
    have h := allN_spec cz i (by rw [e_cnt] at hi; exact hi)
    rw [hall i hi, hid, tA_tab, tblEq_unpack (eT hi) hidc, tblEq_unpack (eT hi) tK_canon]
    rw [bIf_true_right'] at h
    simp only [bOr_eq, Bool.or_assoc] at h
    simp only [Bool.or_assoc]
    exact h
  · rw [all_hRec_iff]
    intro j hj
    rw [tA_tab, commF tK_canon (eT hj)]
    have h := allN_spec ct j (by rw [e_cnt] at hj; exact hj)
    rw [pcommK_eq tK_canon (eT hj)] at h
    exact h
  · have hsz : (Array.filter (involOK 315) (hRec 315 9 J2E.cnt J2E.T J2E.PL).1).size =
        (hRec 315 9 J2E.cnt J2E.T J2E.PL).1.toList.countP (involOK 315) := by
      rw [Array.size_eq_length_toList, Array.toList_filter, List.countP_eq_length_filter]
    rw [hsz, countP_hRec (hi := 1) (q := fun i => involK (J2E.T i)) (by rw [e_cnt]; norm_num)
      (fun i hi => involF (eT hi)), Nat.eq_of_beq_eq_true ci]
    rfl

theorem eCent_ok : j2ECentOK = true := by
  unfold j2ECentOK
  rw [J2Ev.c2_arr, all_hRec_iff]
  intro i hi
  have hT := penumPt_canon (J2Loc.c2_pe i hi)
  have h := allN_spec ecent_ok i hi
  have hg : (j2EGens.all fun e => CFSG.Sporadic.SmallOddCore.commTT 315
      (tabT (unpack 315 9 (J2C2.T i))) e) = allN 4 (fun j => pcommK 315 9 (J2C2.T i) (J2E.GI j)) := by
    apply Bool.eq_iff_iff.2
    rw [eGens_all, CFSG.KS.PEnum.allN_iff _ _]
    refine forall₂_congr fun j hj => ?_
    rw [commF hT (eg_canon hj), pcommK_eq hT (eg_canon hj)]
    rfl
  rw [hg, hid, tA_tab, tblEq_unpack hT hidc, tblEq_unpack hT tK_canon]
  rw [bIf_true_right'] at h
  simp only [bOr_eq, Bool.or_assoc] at h
  simp only [Bool.or_assoc]
  exact h

end CertificateChecks.KernelGH74.J2CentE

end
