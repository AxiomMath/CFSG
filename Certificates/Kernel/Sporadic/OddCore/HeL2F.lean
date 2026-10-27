module

public import Certificates.Kernel.Sporadic.OddCore.HeL2
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.He2276

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.HeldB CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native

theorem idc : canonK 42 6 (mask 6) (42 * 6) (pidn 42 6) = true ∧ idK 42 6 (mask 6) = true ∧
    szOK 42 6 = true := by
  simpa only [bAnd_iff] using id_ok

theorem idTab_eq : idTab 42 = unpack 42 6 (pidn 42 6) := (idK_sound idc.2.1).symm

theorem x_ok : GensOK 42 6 HXE.k HXE.G heXTabs := gensOK_of x_gens

theorem xp {j : Nat} (hj : j < 9) :
    invEqK 42 6 (mask 6) (42 * 6) (HXE.G j) (HXI j) = true ∧
      invEqK 42 6 (mask 6) (42 * 6) (HXI j) (HXE.G j) = true ∧
      canonK 42 6 (mask 6) (42 * 6) (HXI j) = true ∧
      Nat.beq (pcomp 42 6 (mask 6) (HXI j) (HXE.G j)) (pidn 42 6) = true := by
  simpa only [bAnd_iff] using allN_spec x_perm j hj

theorem x_get {j : Nat} (hj : j < 9) :
    heXTabs[j]! = unpack 42 6 (HXE.G j) ∧ canonK 42 6 (mask 6) (42 * 6) (HXE.G j) = true :=
  x_ok.2 j hj

theorem xi_get {j : Nat} (hj : j < 9) : heXInvs[j]! = unpack 42 6 (HXI j) := by
  rw [heXInvs, getElem!_pos _ j (by simp [heXTabs]; omega), Array.getElem_map,
    ← getElem!_pos heXTabs j (by simp [heXTabs]; omega), (x_get hj).1]
  exact (invEqK_sound (xp hj).1).1

theorem x_pt {i : Nat} (hi : i < HXE.cnt) : penumPtK 42 6 (mask 6) (42 * 6) false HXE.G HXE.GI
    HXE.k HXE.cnt HXE.T HXE.PL HXE.POS HXE.SRT HXE.SRI i = true := by
  have e : HXE.cnt = 10752 := rfl
  rcases Nat.lt_or_ge i 2688 with h0 | h0
  · exact penumSl_spec x_sl0 i (Nat.zero_le _) (by omega) hi
  rcases Nat.lt_or_ge i 5376 with h1 | h1
  · exact penumSl_spec x_sl1 i h0 (by omega) hi
  rcases Nat.lt_or_ge i 8064 with h2 | h2
  · exact penumSl_spec x_sl2 i h1 (by omega) hi
  · exact penumSl_spec x_sl3 i h2 (by omega) hi

theorem r_pt {i : Nat} (hi : i < HRE.cnt) : penumPtK 42 6 (mask 6) (42 * 6) false HRE.G HRE.GI
    HRE.k HRE.cnt HRE.T HRE.PL HRE.POS HRE.SRT HRE.SRI i = true := by
  have e : HRE.cnt = 64 := rfl
  exact penumSl_spec r_sl i (Nat.zero_le _) (by omega) hi

theorem words_lt : ∀ j < 6, ∀ i ∈ heRWords.getD j [], i < 9 := by
  decide

theorem r_ok : GensOK 42 6 HRE.k HRE.G heRGens := by
  refine ⟨rfl, fun j hj => ?_⟩
  have hj6 : j < 6 := hj
  obtain ⟨he, hc⟩ := (bAnd_iff _ _).1 (allN_spec r_gens j hj)
  refine ⟨?_, hc⟩
  rw [heRGens, getElem!_pos _ j (by simp; omega), Array.getElem_ofFn, Nat.eq_of_beq_eq_true he,
    lget2_eq]
  exact (wordTabK_eq idTab_eq idc.1 _ (fun l hl => x_get (words_lt j hj6 l hl))).1

theorem x_enum : heXEnum = penumRec 42 6 HXE.cnt HXE.T HXE.PL ∧
    enumOK 42 heXTabs (penumRec 42 6 HXE.cnt HXE.T HXE.PL) = true :=
  penumK_left_sound (cap := 10752) idc.2.2 x_ok x_hd (fun _ hi => x_pt hi)

theorem r_enum : heREnum = penumRec 42 6 HRE.cnt HRE.T HRE.PL ∧
    enumOK 42 heRGens (penumRec 42 6 HRE.cnt HRE.T HRE.PL) = true :=
  penumK_left_sound (cap := 64) idc.2.2 r_ok r_hd (fun _ hi => r_pt hi)

theorem comp42 {p q : Nat} (hp : canonK 42 6 (mask 6) (42 * 6) p = true)
    (hq : canonK 42 6 (mask 6) (42 * 6) q = true) :
    comp 42 (unpack 42 6 p) (unpack 42 6 q) = unpack 42 6 (pcomp 42 6 (mask 6) p q) :=
  compA_unpack hp hq

theorem rec_get {cnt i : Nat} {T PL : Nat → Nat} (hi : i < cnt) :
    (penumRec 42 6 cnt T PL).tabs[i]! = unpack 42 6 (T i) := by
  rw [getElem!_pos _ i (by simp [penumRec, hi])]
  simp [penumRec]

theorem normal : normalOK 42 (penumRec 42 6 HRE.cnt HRE.T HRE.PL).tabs heXTabs heXInvs heRGens =
    true := by
  unfold normalOK
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold invsOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨by simp [heXInvs], ?_⟩
    unfold allBelow
    rw [List.all_eq_true]
    intro k hk
    have hk9 : k < 9 := by simpa [heXTabs] using List.mem_range.1 hk
    obtain ⟨-, -, hci, hpi⟩ := xp hk9
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [xi_get hk9, (x_get hk9).1]
    refine ⟨unpack_size _ _ _, ?_⟩
    rw [comp42 hci (x_get hk9).2, idTab_eq]
    rw [Nat.eq_of_beq_eq_true hpi]
  · unfold allBelow
    rw [List.all_eq_true]
    intro j hj
    have hj9 : j < 9 := by simpa [heXTabs] using List.mem_range.1 hj
    rw [List.all_eq_true]
    intro i hi
    have hi6 : i < 6 := by simpa [heRGens] using List.mem_range.1 hi
    have hn := allN_spec (allN_spec r_norm j hj9) i hi6
    obtain ⟨n1, n2⟩ := (bAnd_iff _ _).1 hn
    rw [strictB_app'] at n1 n2
    obtain ⟨q1, e1⟩ := (bAnd_iff _ _).1 n1
    obtain ⟨q2, e2⟩ := (bAnd_iff _ _).1 n2
    have hg := (r_ok.2 i hi6)
    obtain ⟨-, -, hci, -⟩ := xp hj9
    rw [Bool.and_eq_true, (x_get hj9).1, xi_get hj9, hg.1]
    unfold conjTab
    rw [comp42 (x_get hj9).2 hg.2, comp42 (canonK_pcomp (x_get hj9).2 hg.2) hci,
      comp42 hci hg.2, comp42 (canonK_pcomp hci hg.2) (x_get hj9).2]
    exact ⟨penum_found_sound (fun _ hx => r_pt hx) (Eq.mp Nat.blt_eq q1)
        (Nat.eq_of_beq_eq_true e1),
      penum_found_sound (fun _ hx => r_pt hx) (Eq.mp Nat.blt_eq q2) (Nat.eq_of_beq_eq_true e2)⟩

theorem cent_count :
    ((penumRec 42 6 HXE.cnt HXE.T HXE.PL).tabs.toList.filter (commAll 42 heRGens)).length = 64 := by
  simp only [penumRec, Array.toList_ofFn]
  rw [ofFn_range (m := HXE.cnt) (f := fun i => unpack 42 6 (HXE.T i)), List.filter_map,
    List.length_map, ← List.countP_eq_length_filter]
  have e : HXE.cnt = 64 * 168 := rfl
  rw [e]
  have hk := Nat.eq_of_beq_eq_true x_comm
  rw [cntK_eq] at hk
  refine Eq.trans ?_ hk
  apply List.countP_congr
  intro t ht
  have ht' : t < HXE.cnt := by rw [e]; exact List.mem_range.1 ht
  have hct := penumPt_canon (x_pt ht')
  unfold commAll allBelow
  simp only [Function.comp_apply]
  rw [all_range_iff, allN_iff]
  have hs : heRGens.size = 6 := rfl
  rw [hs]
  refine forall_congr' fun g => imp_congr_right fun hg => ?_
  have hgk := r_ok.2 g hg
  rw [hgk.1, comp42 hct hgk.2, comp42 hgk.2 hct,
    beq_unpack (canonK_pcomp hct hgk.2) (canonK_pcomp hgk.2 hct)]

theorem facts2276 :
    ((∀ j < 9, permChk 42 (heInnerSigma1.getD j #[]) = true ∧
        (heInnerSigma1.getD j #[]).size = 42) ∧
      (∀ j < 6, ∀ i ∈ heRWords.getD j [], i < 9)) ∧
    (enumOK 42 heRGens heREnum = true ∧ heREnum.tabs.size = 64 ∧
      normalOK 42 heREnum.tabs heXTabs heXInvs heRGens = true) ∧
    (enumOK 42 heXTabs heXEnum = true ∧ heXEnum.tabs.size = 10752 ∧
      (heXEnum.tabs.toList.filter (commAll 42 heRGens)).length = 64) := by
  rw [x_enum.1, r_enum.1]
  refine ⟨⟨fun j hj => ?_, words_lt⟩, ⟨r_enum.2, by simp [penumRec]; rfl, normal⟩,
    ⟨x_enum.2, by simp [penumRec]; rfl, cent_count⟩⟩
  have e : heInnerSigma1.getD j #[] = heXTabs[j]! := by
    rw [getElem!_pos heXTabs j (by simp [heXTabs]; omega)]
    simp [heXTabs]
  rw [e, (x_get hj).1]
  obtain ⟨p1, p2, -, -⟩ := xp hj
  refine ⟨?_, unpack_size _ _ _⟩
  unfold permChk
  rw [(invEqK_sound p1).1, (invEqK_sound p1).2, (invEqK_sound p2).2]
  rfl

end CertificateChecks.KernelSpor.He2276

end
