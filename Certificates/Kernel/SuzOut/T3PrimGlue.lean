module

public import Certificates.Kernel.SuzOut.T3Prim
public import Certificates.Kernel.SuzOut.T3Glue
public import CFSG.Certificates.Kernel.HeFixKFix

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzOut.T3P

open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.CatFactsL4U4.SuzCS
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.SuzOut
open CertificateChecks.KernelSuzOut

theorem hid100 : idTab 100 = unpack 100 7 (pidn 100 7) := by
  rw [CFSG.KC.PermTool.idTab_eq]
  exact T3G.idA_eq

theorem gen_facts {j : Nat} (hj : j < 5) : (kGens 3)[j]! = unpack 100 7 (T3X.S j) ∧
    canonK 100 7 (mask 7) (100 * 7) (T3X.S j) = true :=
  ⟨T3G.kGens_get hj, canon_of_perm T3G.szOK' (T3G.permX (by omega))⟩

theorem kw_eq {w : List Nat} (hw : ∀ j ∈ w, j < 5) : wordTab 100 (kGens 3) w = unpack 100 7 (KW w) ∧
    canonK 100 7 (mask 7) (100 * 7) (KW w) = true :=
  wordTabK_eq hid100 T3G.canon_pidn w fun j hj => gen_facts (hw j hj)

theorem letters_of {k : Nat} {w : List Nat} (h : w.all (fun j => Nat.blt j k) = true) :
    ∀ j ∈ w, j < k :=
  fun j hj => Nat.blt_eq.mp (List.all_eq_true.1 h j hj)

theorem hTabs_get {j : Nat} (hj : j < 3) : hTabs[j]! = unpack 100 7 (HK j) ∧
    canonK 100 7 (mask 7) (100 * 7) (HK j) = true := by
  have hl : hWords.length = 3 := by decide
  have hjl : j < hWords.length := by omega
  have hsz : j < (hWords.map (wordTab 100 (kGens 3))).toArray.size := by simpa using hjl
  have hg : hWords.getD j [] = hWords[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
    rfl
  have hk := List.all_eq_true.1 ch23001_h _ (List.getElem_mem hjl)
  unfold hK at hk
  simp only [Bool.and_eq_true] at hk
  have e := kw_eq (letters_of hk.1)
  rw [hTabs, getElem!_pos _ j hsz, List.getElem_toArray, List.getElem_map]
  unfold HK
  rw [hg]
  exact e

theorem root_lt : ∀ l < 3, rootList.getD l 0 < 100 := by decide

theorem primOK_true : primOK = true := by
  unfold primOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [T3G.fix_length]
  · simp [T3G.kGens_size]
  · decide
  · decide
  · decide
  · decide
  · simp only [allBelow, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    intro p hp
    have h := allN_spec ch23001_trans p hp
    unfold transK at h
    simp only [Bool.and_eq_true] at h
    have hw := letters_of h.1
    refine ⟨hw, ?_⟩
    rw [(kw_eq hw).1, CFSG.KC.HeFixK.unpack_getElem! (by decide)]
    exact Nat.eq_of_beq_eq_true h.2
  · simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    intro w hw
    have h := List.all_eq_true.1 ch23001_h w hw
    unfold hK at h
    simp only [Bool.and_eq_true] at h
    have hl := letters_of h.1
    refine ⟨hl, ?_⟩
    rw [(kw_eq hl).1, CFSG.KC.HeFixK.unpack_getElem! (by decide)]
    exact Nat.eq_of_beq_eq_true h.2
  · simp only [allBelow, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    intro p hp
    have h := allN_spec ch23001_u p hp
    unfold uK at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hlab, hlet, hb⟩ := h
    have hl3 := Nat.blt_eq.mp hlab
    have hw := letters_of hlet
    have e := wordTabK_eq (S := HK) (gs := hTabs) hid100 T3G.canon_pidn (uWords.getD p [])
      fun j hj => hTabs_get (hw j hj)
    refine ⟨⟨hl3, hw⟩, ?_⟩
    unfold wordTab
    rw [e.1,CFSG.KC.HeFixK.unpack_getElem! (root_lt _ hl3)]
    exact Nat.eq_of_beq_eq_true hb
  · decide
  · decide
  · decide

end CertificateChecks.KernelSuzOut.T3P

end
