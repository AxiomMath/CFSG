module

public import Certificates.Kernel.J2Cover.KFact17260
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.LocalComp.Child3Lemmas
public import CFSG.Certificates.Kernel.J2CoverSound
public import Certificates.Data.Kernel.Spor.BaseMask

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover.KF17260

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.Child3 CFSG.KC.BfsPin CFSG.KS.BaseMask
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.J2Cover (inP commA arrTable twoAArr)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

theorem elt_of {t : Array Nat} {X XI : Nat} (ht : t = unpack 315 9 X) (h : eltK X XI = true) :
    isInvA 315 t (invCand 315 t) = true ∧ inP t = true ∧ invCand 315 t = unpack 315 9 XI ∧
      CnN 315 9 X ∧ CnN 315 9 XI ∧ invEqK 315 9 (mask 9) (315 * 9) X XI = true := by
  unfold eltK sP cK at h
  simp only [bAnd_iff] at h
  obtain ⟨hc, hci, hinv, hz, hs⟩ := h
  obtain ⟨e1, e2⟩ := invEqK_sound hinv
  subst ht
  exact ⟨by rw [e1]; exact e2, inP_of rfl hz (range_of_canonK hc) hs, e1, hc, hci, hinv⟩

theorem ordTest_of {X m : Nat} (hm : 0 < m) (hX : CnN 315 9 X) :
    ordTest 315 m (arrTable 315 (unpack 315 9 X)) = ordPK 315 9 m (prodK 315 9 [X]) := by
  unfold ordTest
  exact ordW_unpack (ws := [X]) hm fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX

theorem commA_of {X Y : Nat} (hX : CnN 315 9 X) (hY : CnN 315 9 Y) :
    commA (unpack 315 9 X) (unpack 315 9 Y) = Nat.beq (pc X Y) (pc Y X) := by
  unfold commA
  rw [compA_unpackN hX hY, compA_unpackN hY hX, eqA_unpackN (canon_pcN hX hY) (canon_pcN hY hX)]
  rfl

theorem arrTable_unpack (X : Nat) : arrTable 315 (unpack 315 9 X) = tabT (unpack 315 9 X) := by
  apply Array.ext (by simp [CFSG.ComponentClassification.J2Cover.arrTable, tabT, unpack])
  intro i h1 h2
  simp [CFSG.ComponentClassification.J2Cover.arrTable, tabT, unpack]

theorem binds : (∀ i < 3, kf2Arrs[i]! = unpack 315 9 (KF i)) ∧
    (∀ i < 3, invReps[i]! = unpack 315 9 (RP i)) ∧
    (∀ j < 4, p3List[j]! = unpack 315 9 (P3.GI j)) := by
  have h := ch17260bind
  simp only [bAnd_iff] at h
  exact ⟨fun i hi => arrBind_sound (allN_spec h.1 i hi),
    fun i hi => arrBind_sound (allN_spec h.2.1 i hi),
    fun j hj => arrBind_sound (allN_spec h.2.2 j hj)⟩

theorem rp_canon : ∀ i < 3, CnN 315 9 (RP i) := by
  intro i hi
  have h := allN_spec ch17260kf2 i hi
  unfold kf2K at h
  simp only [bAnd_iff] at h
  exact h.2.1

theorem kf2 : kf2Check = true := by
  unfold kf2Check
  rw [List.all_eq_true]
  intro i hi
  have hi3 : i < 3 := List.mem_range.1 hi
  have h := allN_spec ch17260kf2 i hi3
  unfold kf2K at h
  simp only [bAnd_iff] at h
  obtain ⟨he, hcr, ho⟩ := h
  obtain ⟨i1, i2, i3, c1, c2, -⟩ := elt_of (binds.1 i hi3) he
  simp only [Bool.and_eq_true]
  refine ⟨⟨i1, i2⟩, ?_⟩
  have c3 := canon_pcN c2 hcr
  have c4 := canon_pcN c3 c1
  rw [i3, binds.1 i hi3, binds.2.1 i hi3, compA_unpackN c2 hcr, compA_unpackN c3 c1,
    compA_unpackN hcr c4, ordTest_of (by norm_num) (canon_pcN hcr c4)]
  exact ho

theorem p3_elt : ∀ j < 4, isInvA 315 p3List[j]! (invCand 315 p3List[j]!) = true ∧
    inP p3List[j]! = true ∧ CnN 315 9 (P3.GI j) ∧ CnN 315 9 (P3I j) ∧
    invEqK 315 9 (mask 9) (315 * 9) (P3.GI j) (P3I j) = true ∧
    Nat.beq (pc (P3.GI j) (P3.GI 0)) (pc (P3.GI 0) (P3.GI j)) = true := by
  intro j hj
  have h := allN_spec ch17260p3 j hj
  unfold p3K at h
  simp only [bAnd_iff] at h
  obtain ⟨a, b, -, c, d, e⟩ := elt_of (binds.2.2 j hj) h.1
  exact ⟨a, b, c, d, e, h.2⟩

theorem hy0 : y0Arr = unpack 315 9 (P3.GI 0) := binds.2.2 0 (by norm_num)

theorem y0 : y0Check = true := by
  obtain ⟨i1, i2, c1, -, -, -⟩ := p3_elt 0 (by norm_num)
  have hta : twoAArr = unpack 315 9 (RP 1) := binds.2.1 1 (by norm_num)
  have hy := ch17260y0
  simp only [bAnd_iff] at hy
  unfold y0Check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨i1, i2⟩, ?_⟩, ?_⟩
  · rw [hy0, hta, commA_of c1 (rp_canon 1 (by norm_num))]
    exact hy.1
  · rw [hy0, ordTest_of (by norm_num) c1]
    exact hy.2

theorem mem_p3 {g : Array Nat} (hg : g ∈ p3List) : ∃ j < 4, g = p3List[j]! := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hl : p3List.length = 4 := rfl
  exact ⟨j, by omega, (getElem!_pos p3List j hj).symm⟩

theorem p3_tabs : TabsOK 315 9 4 P3.GI p3Tbls.toArray := by
  refine ⟨rfl, fun j hj => ⟨?_, (p3_elt j hj).2.2.1⟩⟩
  rw [← arrTable_unpack, ← binds.2.2 j hj]
  interval_cases j <;> rfl

theorem p3_enum : CFSG.Sporadic.SmallOddCore.enumOK 315 100 27 p3Tbls = true := by
  have h := ch17260rec
  simp only [bAnd_iff] at h
  obtain ⟨hn, hG, hh, hc⟩ := h
  exact enumOK_of hn (fun j hj => Nat.eq_of_beq_eq_true (allN_spec hG j hj)) p3_tabs
    (fun j hj => ⟨(p3_elt j hj).2.2.2.2.1, (p3_elt j hj).2.2.2.1⟩) hh
    (fun i hi => penumSl_spec ch17260pe i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec ch17260hs i (Nat.zero_le _) (by omega) hi)
    (fun c hc => slK_spec ch17260cl c (Nat.zero_le _) (by rw [Nat.zero_add]; exact hc) hc)
    (Nat.eq_of_beq_eq_true hc)

theorem p3 : p3Check = true := by
  unfold p3Check
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, p3_enum⟩, ?_⟩
  · rw [List.all_eq_true]
    intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_p3 hg
    obtain ⟨a, b, c, -, -, e⟩ := p3_elt j hj
    simp only [Bool.and_eq_true]
    refine ⟨⟨a, b⟩, ?_⟩
    rw [binds.2.2 j hj, hy0, commA_of c (p3_elt 0 (by norm_num)).2.2.1]
    exact e
  · rw [List.all_eq_true]
    intro g hg
    obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list p3_tabs hg
    exact permOK_unpack hc (p3_elt j hj).2.2.2.2.1
  · have e1 : p3a = unpack 315 9 (P3.GI 1) := binds.2.2 1 (by norm_num)
    have e3 : p3c = unpack 315 9 (P3.GI 3) := binds.2.2 3 (by norm_num)
    rw [e1, e3, commA_of (p3_elt 1 (by norm_num)).2.2.1 (p3_elt 3 (by norm_num)).2.2.1]
    have hn := ch17260nc
    cases h : Nat.beq (pc (P3.GI 1) (P3.GI 3)) (pc (P3.GI 3) (P3.GI 1))
    · rfl
    · rw [h] at hn
      exact absurd hn Bool.false_ne_true

theorem facts17260 : kf2Check = true ∧ y0Check = true ∧ p3Check = true := ⟨kf2, y0, p3⟩

end CertificateChecks.KernelJ2Cover.KF17260

end
