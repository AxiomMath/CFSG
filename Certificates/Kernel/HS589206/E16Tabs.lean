module

public import Certificates.Kernel.HS589206.E16Gen
public import Certificates.Kernel.HS589206.E16RecA
public import Certificates.Kernel.HS589206.E16RecB
public import Certificates.Kernel.HS589206.E16Rec5
public import Certificates.Kernel.HS589207.Tabs
public import CFSG.Certificates.Kernel.DcSubK

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HS589206.E16Tabs

open CFSG.KC.DcHSOutK CFSG.KC.E64F CFSG.KC.DcK CFSG.KD.HS589206.E16 CFSG.KD.HS589207
  CFSG.KD.HS589207.Tabs CFSG.Quasithin.H13.LocDbl.HSLoc CFSG.Quasithin.H13.LocDbl.DcNative

theorem good_tabsOf {ws : List (List Nat)} (hws : ∀ w ∈ ws, ∀ l ∈ w, l < 4) {L : Nat → Nat → Nat}
    (hL : ∀ t < ws.length, ∀ q < 100, L t q = wordF A (ws.getD t []) q) :
    ∀ t < (tabsOf ws).size, Good 100 ((tabsOf ws).getD t #[]) (L t) := by
  intro t ht
  have ht' : t < ws.length := by simpa [tabsOf] using ht
  have hm : ws.getD t [] ∈ ws := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
    exact List.getElem_mem ht'
  have e : (tabsOf ws).getD t #[] = tabW 100 AB (ws.getD t []) := by
    simp [tabsOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, ht']
  rw [e]
  exact good_congr (good_tabW fun l hl => good_AB l (hws _ hm l hl)) fun q hq => (hL t ht' q hq).symm

theorem gens' : ∀ t < 3, (∀ q < 100, GS t q = wordF A (sWords.getD t []) q) ∧
    ∀ q < 100, GS5 t q = wordF A (s5Words.getD t []) q := by
  intro t ht
  have h := CFSG.KS.allN_spec E16Gen.gens t ht
  simp only [Bool.and_eq_true] at h
  exact ⟨eqF_spec h.1, eqF_spec h.2⟩

theorem sWords_lt4 : ∀ w ∈ sWords, ∀ l ∈ w, l < 4 := by decide +kernel

theorem s5Words_lt4 : ∀ w ∈ s5Words, ∀ l ∈ w, l < 4 := by decide +kernel

theorem good_sTabs : ∀ t < sTabs.size, Good 100 (sTabs.getD t #[]) (GS t) :=
  good_tabsOf sWords_lt4 fun t ht => (gens' t (by simpa [sWords] using ht)).1

theorem good_s5Tabs : ∀ t < s5Tabs.size, Good 100 (s5Tabs.getD t #[]) (GS5 t) :=
  good_tabsOf s5Words_lt4 fun t ht => (gens' t (by simpa [s5Words] using ht)).2

theorem sElemK : ∀ k < 512, elemK 100 B100 GS 3 ES k = true := by
  intro k hk
  have sl : ∀ lo, elemsK 100 B100 GS 3 ES lo 256 = true → lo ≤ k → k < lo + 256 →
      elemK 100 B100 GS 3 ES k = true := fun lo h h1 h2 => by
    unfold elemsK at h
    rw [List.all_eq_true] at h
    exact h k (List.mem_range'_1.2 ⟨h1, h2⟩)
  by_cases h1 : k < 256
  · exact sl 0 E16RecA.s0 (by omega) (by omega)
  · exact sl 256 E16RecB.s1 (by omega) (by omega)

theorem s5ElemK : ∀ k < 125, elemK 100 B100 GS5 3 ES5 k = true := by
  intro k hk
  have h := E16Rec5.s0
  unfold elemsK at h
  rw [List.all_eq_true] at h
  exact h k (List.mem_range'_1.2 ⟨Nat.zero_le k, by omega⟩)

theorem sTabs_size : sTabs.size = 3 := rfl

theorem s5Tabs_size : s5Tabs.size = 3 := rfl

theorem mTabs_size : mTabs.size = 2 := rfl

theorem enum_S : subEnumOK 100 B100 ES.N 600 sTabs = true :=
  subEnumOK_of_elemK good_sTabs (by rw [sTabs_size]; decide) E16RecA.hd
    (by rw [sTabs_size]; exact sElemK)

theorem enum_S5 : subEnumOK 100 B100 ES5.N 200 s5Tabs = true :=
  subEnumOK_of_elemK good_s5Tabs (by rw [s5Tabs_size]; decide) E16Rec5.hd
    (by rw [s5Tabs_size]; exact s5ElemK)

theorem enum_M : subEnumOK 100 B100 EM.N 12000 mTabs = true :=
  subEnumOK_of_elemK good_mTabs (by rw [mTabs_size]; decide) MRecA.hd
    (by rw [mTabs_size]; exact mElemK)

end CFSG.KD.HS589206.E16Tabs

end
