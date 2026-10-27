module

public import Certificates.Kernel.HS589207.Gen
public import Certificates.Kernel.HS589207.MRecA
public import Certificates.Kernel.HS589207.MRecB
public import Certificates.Kernel.Misc.Perm.HS100.BaseGlue
public import CFSG.Certificates.Kernel.DcHSOutKSound
public import CFSG.Certificates.Kernel.DcKSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HS589207.Tabs

open CFSG.KC.DcHSOutK CFSG.KC.E64F CFSG.KC.Enum CFSG.Quasithin.H13.LocDbl.HSLoc
  CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank
  CertificateChecks.KernelMisc.HS100

theorem eqF_spec {f g : Nat → Nat} (h : eqF f g = true) : ∀ q < 100, f q = g q :=
  fun q hq => Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h q hq)

theorem ltF_spec {f : Nat → Nat} (h : ltF f = true) : ∀ q < 100, f q < 100 := fun q hq => by
  have := CFSG.KS.allN_spec h q hq
  simpa [Nat.blt_eq] using this

theorem good_congr {t : Array Nat} {f g : Nat → Nat} (ht : Good 100 t f)
    (h : ∀ q < 100, f q = g q) : Good 100 t g :=
  ⟨ht.1, fun p hp => by rw [← h p hp]; exact ht.2 p hp⟩

theorem good_unpack {X : Nat} (h : ltF (h7 X) = true) :
    Good 100 (CFSG.KS.Raw.unpack 100 7 X) (h7 X) := by
  refine ⟨by simp [CFSG.KS.Raw.unpack], fun p hp => ⟨?_, ltF_spec h p hp⟩⟩
  simp [CFSG.KS.Raw.unpack, Array.getD_eq_getD_getElem?, hp, h7]

theorem getD_toArray_map (f : Nat → Nat) {N k : Nat} (hk : k < N) :
    ((List.range N).map f).toArray.getD k 0 = f k := by
  simp [Array.getD_eq_getD_getElem?, hk]

theorem gens' : (∀ l < 4, ltF (A l) = true) ∧ ltF uF = true ∧
    (∀ q < 100, A 0 (A 2 q) = q) ∧ (∀ q < 100, A 2 (A 0 q) = q) ∧
    (∀ q < 100, A 1 (A 3 q) = q) ∧ (∀ q < 100, A 3 (A 1 q) = q) := by
  have h := Gen.gens
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨CFSG.KS.allN_spec h1, h2, eqF_spec h3, eqF_spec h4, eqF_spec h5, eqF_spec h6⟩

theorem A_lt {l : Nat} (hl : l < 4) {q : Nat} (hq : q < 100) : A l q < 100 :=
  ltF_spec (gens'.1 l hl) q hq

theorem A_inv {l : Nat} (hl : l < 4) {q : Nat} (hq : q < 100) :
    A (CFSG.KC.DcHSOutK.invL l) (A l q) = q ∧ A l (A (CFSG.KC.DcHSOutK.invL l) q) = q := by
  obtain ⟨-, -, h02, h20, h13, h31⟩ := gens'
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · exact ⟨h20 q hq, h02 q hq⟩
  · exact ⟨h31 q hq, h13 q hq⟩
  · exact ⟨h02 q hq, h20 q hq⟩
  · exact ⟨h13 q hq, h31 q hq⟩

theorem good_ta : Good 100 ta (A 0) := by
  have e : A 0 = h7 (HX.F 0) := funext fun _ => rfl
  rw [e, ta, hs100Arr_eq 0 (by norm_num)]
  exact good_unpack (e ▸ gens'.1 0 (by norm_num))

theorem good_tb : Good 100 tb (A 1) := by
  have e : A 1 = h7 (HX.F 1) := funext fun _ => rfl
  rw [e, tb, hs100Arr_eq 1 (by norm_num)]
  exact good_unpack (e ▸ gens'.1 1 (by norm_num))

theorem good_uTab : Good 100 uTab uF := by
  rw [uTab, hs100Arr_eq 15 (by norm_num)]
  exact good_unpack gens'.2.1

theorem good_AB : ∀ l < 4, Good 100 (AB.getD l #[]) (A l) := by
  intro l hl
  obtain ⟨-, -, h02, h20, h13, h31⟩ := gens'
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · change Good 100 ta (A 0)
    exact good_ta
  · change Good 100 tb (A 1)
    exact good_tb
  · change Good 100 (invT ta) (A 2)
    exact good_invT good_ta (fun p hp => A_lt (by norm_num) hp) h20 h02
  · change Good 100 (invT tb) (A 3)
    exact good_invT good_tb (fun p hp => A_lt (by norm_num) hp) h31 h13

theorem AB_size : AB.size = 4 := rfl

theorem good_mTabs : ∀ t < mTabs.size, Good 100 (mTabs.getD t #[]) (GM t) := by
  intro t ht
  have hm := Gen.mgens
  simp only [Bool.and_eq_true] at hm
  have h2 : mTabs.size = 2 := rfl
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · have e : mTabs.getD 0 #[] = tabW 100 AB (mWords.getD 0 []) := rfl
    rw [e]
    refine good_congr (CFSG.KC.DcK.good_tabW fun l hl => good_AB l ?_) fun q hq =>
      (eqF_spec hm.1 q hq).symm
    revert l
    decide
  · have e : mTabs.getD 1 #[] = tabW 100 AB (mWords.getD 1 []) := rfl
    rw [e]
    refine good_congr (CFSG.KC.DcK.good_tabW fun l hl => good_AB l ?_) fun q hq =>
      (eqF_spec hm.2 q hq).symm
    revert l
    decide

theorem mElemK : ∀ k < 11520, CFSG.KC.DcK.elemK 100 B100 GM 2 EM k = true := by
  intro k hk
  have sl : ∀ lo, CFSG.KC.DcK.elemsK 100 B100 GM 2 EM lo 1440 = true → lo ≤ k →
      k < lo + 1440 → CFSG.KC.DcK.elemK 100 B100 GM 2 EM k = true := fun lo h h1 h2 => by
    unfold CFSG.KC.DcK.elemsK at h
    rw [List.all_eq_true] at h
    exact h k (List.mem_range'_1.2 ⟨h1, h2⟩)
  by_cases h1 : k < 1440
  · exact sl 0 MRecA.s0 (by omega) (by omega)
  by_cases h2 : k < 2880
  · exact sl 1440 MRecA.s1 (by omega) (by omega)
  by_cases h3 : k < 4320
  · exact sl 2880 MRecA.s2 (by omega) (by omega)
  by_cases h4 : k < 5760
  · exact sl 4320 MRecA.s3 (by omega) (by omega)
  by_cases h5 : k < 7200
  · exact sl 5760 MRecB.s4 (by omega) (by omega)
  by_cases h6 : k < 8640
  · exact sl 7200 MRecB.s5 (by omega) (by omega)
  by_cases h7 : k < 10080
  · exact sl 8640 MRecB.s6 (by omega) (by omega)
  · exact sl 10080 MRecB.s7 (by omega) (by omega)

theorem bfsM : bfsEnumL 100 B100 mTabs 12000 =
    (((List.range 11520).map EM.par).toArray, ((List.range 11520).map EM.lab).toArray) :=
  CFSG.KC.DcK.bfsEnumL_of_elemK good_mTabs (by decide) MRecA.hd mElemK

theorem elemK_row {k : Nat} (h : CFSG.KC.DcK.elemK 100 B100 GM 2 EM k = true) :
    (k = 0 → EM.row 0 = B100) ∧
      (k ≠ 0 → EM.par k < k ∧ EM.lab k < 2 ∧ EM.row k = (EM.row (EM.par k)).map (GM (EM.lab k))) := by
  unfold CFSG.KC.DcK.elemK at h
  by_cases hk : k = 0
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
    simp only [and_assoc] at h
    exact ⟨fun _ => h.1, fun h0 => absurd rfl h0⟩
  · have hk' : (k == 0) = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    simp only [and_assoc] at h
    exact ⟨fun h0 => absurd h0 hk, fun _ => ⟨h.1, h.2.1, h.2.2.1⟩⟩

theorem row_getD (k : Nat) {q : Nat} (hq : q < 100) : (EM.row k).getD q 0 = mF k q := by
  simp [EM, CFSG.KC.DcK.recK, List.getD_eq_getElem?_getD, hq, mF, fl]

theorem mF_lt : ∀ k < 11520, ∀ q < 100, mF k q < 100 := by
  intro k hk q hq
  by_cases h : k < 5760
  · have := CFSG.KS.allBlk_spec MRecA.lt0 k h
    have e : Nat.add 0 k = k := Nat.zero_add k
    rw [e] at this
    exact ltF_spec this q hq
  · have := CFSG.KS.allBlk_spec MRecB.lt1 (k - 5760) (by omega)
    have e : Nat.add 5760 (k - 5760) = k := by
      change 5760 + (k - 5760) = k
      omega
    rw [e] at this
    exact ltF_spec this q hq

theorem mElems_eq : mElems = enumTabs mTabs
    (((List.range 11520).map EM.par).toArray, ((List.range 11520).map EM.lab).toArray) 11520 := by
  unfold mElems
  rw [bfsM]

theorem good_mElems : ∀ k < 11520, Good 100 (mElems.getD k #[]) (mF k) := by
  rw [mElems_eq]
  refine enumTabs_good good_mTabs (fun q hq => ?_) (fun k hk0 hk => ?_) mF_lt
  · have h := (elemK_row (mElemK 0 (by norm_num))).1 rfl
    rw [← row_getD 0 hq, h]
    simp [B100, List.getD_eq_getElem?_getD, hq]
  · obtain ⟨hp, hl, hr⟩ := (elemK_row (mElemK k hk)).2 (by omega)
    rw [getD_toArray_map _ hk, getD_toArray_map _ hk]
    refine ⟨hp, hl, fun q hq => ?_⟩
    rw [← row_getD k hq, ← row_getD _ hq, hr]
    have hlen : q < (EM.row (EM.par k)).length := by simp [EM, CFSG.KC.DcK.recK, hq]
    simp [List.getD_eq_getElem?_getD, hlen]

theorem mElems_size : mElems.size = 11520 := by
  rw [mElems_eq]
  simp [enumTabs]

end CFSG.KD.HS589207.Tabs

end
