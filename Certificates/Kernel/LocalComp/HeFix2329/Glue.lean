module

public import Certificates.Kernel.LocalComp.HeFix2329.ClosK
public import Certificates.Kernel.LocalComp.HeFix2329.Chk32
public import Certificates.Kernel.LocalComp.HeAutPin
public import CFSG.Certificates.Kernel.HeFixKSound
public import CFSG.Certificates.Kernel.HeFixKFix

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeFix2329

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool CFSG.KC.HexaK
open CFSG.KC.HeFixK CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native
open CertificateChecks.KernelLC CertificateChecks.KernelLC.HeFix

theorem kS0 : decS 5 14 SA SB 0 = (List.range 32, heBase) := by decide +kernel

theorem kClos_all {j : Nat} (hj : j < 6) :
    closK 8330 14 5 2048 SA SB SM (Q j) (T0K j) j = true := by
  match j, hj with
  | 0, _ => exact kClos0
  | 1, _ => exact kClos1
  | 2, _ => exact kClos2
  | 3, _ => exact kClos3
  | 4, _ => exact kClos4
  | 5, _ => exact kClos5

theorem hfS_closed : ∃ S : Finset (List ℕ × List ℕ), S.card ≤ 2048 ∧ (List.range 32, heBase) ∈ S ∧
    ∀ j < 6, ∀ p ∈ S,
      (p.1.map (fun x => (hfT0Tabs32[j]!)[x]!), p.2.map (fun x => (hfT0Tabs[j]!)[x]!)) ∈ S := by
  refine ⟨setS 5 14 2048 SA SB, card_setS _ _ _ _ _, kS0 ▸ decS_mem (by decide), fun j hj p hp => ?_⟩
  rw [hfT0Tabs32_get.2 j hj, (T0_get hj).1]
  exact closK_sound (kClos_all hj) p hp

theorem hfT0Tabs_lt5 {j : Nat} (hj : j < 5) : hfT0Tabs[j]! = hfTTabs[j]! := by
  rw [hfT0Tabs, ofFn_get _ (by omega : j < 6)]
  simp [hj]

theorem cnT0 {j : Nat} (hj : j < 6) : canonK 8330 14 (mask 14) (8330 * 14) (T0K j) = true :=
  (T0_get hj).2

theorem hfDelta_pres : ∀ j < 6, ∀ x ∈ hfDelta32, (hfT0Tabs[j]!)[x]! ∈ hfDelta32 := by
  intro j hj x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hres : hfRes hfT0Tabs[j]! = unpack 32 6 (Q j) := by
    rw [← map_get hfRes hfT0Tabs (by simpa [hfT0Tabs] using hj)]
    exact hfT0Tabs32_get.2 j hj
  have hk32 : k < 32 := delta_len ▸ hk
  have e := congrArg (·[k]!) hres
  simp only [hfRes, restrictArr] at e
  rw [unpack_getElem! hk32, getElem!_pos _ k (by simpa using hk), List.getElem_toArray,
    List.getElem_map] at e
  have hlt := e ▸ pg_lt_of_canonK (allN_spec kCanonQ j hj) hk32
  rw [← delta_len] at hlt
  exact List.idxOf_lt_length_iff.1 hlt

theorem hfEA_eq : hfEATab = unpack 8330 14 (wordTabK 8330 14 T0K [3, 2]) := by
  have hw : hfEWords.getD 1 [] = [3, 2] := rfl
  rw [hfEATab, hw]
  refine wordTabS_unpack hid hidA _ (fun k hk => cnT0 (by simp at hk; omega)) fun k hk => ?_
  have hk5 : k < 5 := by simp at hk; omega
  rw [← hfT0Tabs_lt5 hk5]
  exact (T0_get (by omega)).1

theorem hfFix346 : (List.range 8330).countP (fun i => hfEATab[i]! == i) = 346 := by
  rw [hfEA_eq, countP_fix]
  exact Nat.eq_of_beq_eq_true kFix

theorem hfDelta32_facts :
    hfDelta32.length = 32 ∧ (∀ x ∈ hfDelta32, x < 8330) ∧ hfDelta32.Nodup :=
  ⟨delta_len, delta_lt, by decide⟩

theorem tTabs32_get {k : Nat} (hk : k < 5) : hfTTabs32[k]! = unpack 32 6 (Q k) := by
  have h5 : hfTTabs.size = 5 := by simp [hfTTabs]
  rw [hfTTabs32, map_get _ _ (by omega)]
  have e : hfTTabs[k]! = hfT0Tabs[k]! := (hfT0Tabs_lt5 hk).symm
  rw [e, ← map_get hfRes hfT0Tabs (by simp [hfT0Tabs]; omega)]
  exact hfT0Tabs32_get.2 k (by omega)

theorem cnQ5 {k : Nat} (hk : k < 5) : canonK 32 6 (mask 6) (32 * 6) (Q k) = true :=
  allN_spec kCanonQ k (by omega)

theorem pinT : Pin 32 6 hfTTabs32.toList HeT32.ng HeT32.G HeT32.N HeT32.T HeT32.E HeT32.S := by
  have hg := kGT
  simp only [Bool.and_eq_true] at hg
  have hng : HeT32.ng = 5 := Nat.eq_of_beq_eq_true hg.1
  have hp := kPerm32
  simp only [Bool.and_eq_true] at hp
  refine ⟨?_, fun k hk => ?_, allN_spec hp.1, HeT32.ok, by decide⟩
  · rw [Array.toArray_toList, hng]
    simp [hfTTabs32, hfTTabs]
  · rw [hng] at hk
    rw [Array.toArray_toList, tTabs32_get hk, Nat.eq_of_beq_eq_true (allN_spec hg.2 k hk)]

theorem pinE : Pin 32 6 hfETabs32.toList HeE32.ng HeE32.G HeE32.N HeE32.T HeE32.E HeE32.S := by
  have hg := kGE
  simp only [Bool.and_eq_true] at hg
  have hng : HeE32.ng = 6 := Nat.eq_of_beq_eq_true hg.1
  have hp := kPerm32
  simp only [Bool.and_eq_true] at hp
  have hid := kId32
  simp only [Bool.and_eq_true] at hid
  refine ⟨?_, fun k hk => ?_, allN_spec hp.2, HeE32.ok, by decide⟩
  · rw [Array.toArray_toList, hng]
    simp [hfETabs32]
  · rw [hng] at hk
    have hw : ∀ j ∈ hfEWords.getD k [], j < 5 := by
      match k, hk with
      | 0, _ => decide
      | 1, _ => decide
      | 2, _ => decide
      | 3, _ => decide
      | 4, _ => decide
      | 5, _ => decide
    rw [Array.toArray_toList, Nat.eq_of_beq_eq_true (allN_spec hg.2 k hk), hfETabs32,
      ofFn_get _ hk]
    exact wordTabS_unpack hid.1 (idK_sound hid.2).symm _ (fun j hj => cnQ5 (hw j hj))
      fun j hj => tTabs32_get (hw j hj)

theorem pinA : Pin 32 6 hfT0Tabs32.toList HeAutY.ng HeAutY.G HeAutY.N HeAutY.T HeAutY.E
    HeAutY.S := by
  have kp := HeAutCheck.kPermG
  simp only [Bool.and_eq_true] at kp
  exact HeAutCheck.pinY kp.1.1.1.1

theorem hfSylow32_true :
    enumOK 32 hfTTabs32 hfTEnum32 = true ∧ hfTEnum32.tabs.size = 1024 ∧
      enumOK 32 hfT0Tabs32 hfT0Enum32 = true ∧ hfT0Enum32.tabs.size = 2048 ∧
      (hfTEnum32.tabs.toList.filter (commAll 32 hfTTabs32)).length = 2 ∧
      enumOK 32 hfETabs32 hfEEnum32 = true ∧ hfEEnum32.tabs.size = 64 ∧
      (∀ i < 6, ∀ j < 6, comp 32 hfETabs32[i]! hfETabs32[j]! =
        comp 32 hfETabs32[j]! hfETabs32[i]!) ∧
      (∀ i < 6, comp 32 hfETabs32[i]! hfETabs32[i]! = idTab 32) ∧
      normalOK 32 hfEEnum32.tabs hfTTabs32 (hfTTabs32.map (invTab 32)) hfETabs32 = true ∧
      hfOuterE8Check 32 hfTEnum32.tabs hfT0Enum32.tabs = true := by
  have hg := kGE
  simp only [Bool.and_eq_true] at hg
  have ho : 0 < outerK HeAutY.N HeAutY.T HeT32.N HeT32.T IT WT := by
    rw [Nat.eq_of_beq_eq_true kOuter]
    decide
  exact hfSylow32_iff.2 (sylow32K_sound pinT pinA pinE ⟨rfl, rfl, rfl⟩
    (Nat.eq_of_beq_eq_true hg.1) (Nat.eq_of_beq_eq_true kCen) kE kNorm kIT ho)

end CertificateChecks.KernelLC.HeFix2329

end
