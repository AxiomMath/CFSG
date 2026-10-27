module

public import Certificates.Kernel.S63K.LChecks
public import Certificates.Kernel.S63K.I21111
public import Certificates.Kernel.S63K.G4235
public import CFSG.Certificates.Kernel.S63K.ClassBfsSound

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.L4234

open CFSG.D4Hex CFSG.LargeExtraspecial.S63 CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KC.Enum CFSG.KS
  CFSG.KS.SporSch.M24 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CertificateChecks.KernelS63
  CertificateChecks.KernelS63.HD CertificateChecks.KernelS63.GD

theorem z0_eq : z0R = unpackR 24 (ID.ZP 0) := by
  rw [z0R, I21111.word_eq (by decide), unpackR_mod, I21111.roots.1]

theorem hK : ClassK ID.G ID.ZP LK.PAR LK.LAB LK.W ID.ZS 8 819 := (classK_of_bfsK LK.zbfs).1

theorem cz_eq : mkClass d4Gens z0R = CkG ID.ZP LK.PAR LK.LAB 819 :=
  mkClass_of_K ID.gens_size ID.gens_eq z0_eq hK

theorem gensOK_d4 : gensOK d4Gens = true := by
  unfold gensOK
  rw [allLt_iff, ID.gens_size]
  intro k hk
  have h := MatL.allN_iff.1 ID.invG k hk
  have e : CFSG.KC.F2W.mulW 24 (ID.G k) (ID.G k) % 2 ^ 576 = idP := by
    rw [← idM_eq, ← shiftLeft_576]
    exact Nat.eq_of_beq_eq_true h
  rw [ID.gens_eq k hk, mulR_unpackR, unpackR_mod, e, ← oneR_eq]
  exact beq_self_eq_true _

theorem w_eq {i j : ℕ} (hj : j < 8) : LK.W (i * 8 + j) = im j i := by
  have e1 : (i * 8 + j) % 8 = j := by omega
  have e2 : (i * 8 + j) / 8 = i := by omega
  unfold LK.W
  exact congrArg₂ im e1 e2

theorem link : linkCheckOn (mkClass d4Gens z0R) = true := by
  rw [cz_eq]
  unfold linkCheckOn
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨gensOK_d4, classTreeOK_of_K ID.gens_size ID.gens_eq z0_eq hK⟩, ?_⟩, permArrs_size⟩,
    ?_⟩
  · simp [CkG, ElG]
  · rw [allLt_iff]
    intro j hj
    rw [allLt_iff]
    intro i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    obtain ⟨h1, h2⟩ := clos_of_C hK i hi j hj
    rw [w_eq hj] at h1 h2
    rw [perm_get hj hi]
    refine ⟨h1, ?_⟩
    change (ElG ID.ZP 819)[im j i]! = conjR d4Gens[j]! (ElG ID.ZP 819)[i]!
    rw [elG_get h1, elG_get hi, ID.gens_eq j hj, conjR_unpackR, h2]

theorem lnPt0 (l : ℕ) : lnPt l 0 = LTf (3 * l) := G4235.hP _

theorem lnPt1 (l : ℕ) : lnPt l 1 = LTf (3 * l + 1) := G4235.hP _

theorem lnPt2 (l : ℕ) : lnPt l 2 = LTf (3 * l + 2) := G4235.hP _

theorem lineIndex_eq : lineIndex = hexLineKeyMap lineTab := by
  unfold lineIndex hexLineKeyMap lnPt CFSG.D4Hex.lineKey
  rfl

theorem lk_eq (v : ℕ) : CFSG.KC.S63K.lineKey lineTab v = keyF LTf v := by
  unfold CFSG.KC.S63K.lineKey keyF
  rw [G4235.hP, G4235.hP, G4235.hP]

theorem idx_key {v : ℕ} (hv : v < 2457) : lineIndex.getD (keyF LTf v) 0 = v := by
  rw [lineIndex_eq, ← lk_eq]
  exact keyMap_getD (fun a ha b hb e => G4235.keys_inj a ha b hb (by rwa [lk_eq, lk_eq] at e)) 0
    hv

theorem sortKey_eq (a b c : ℕ) : CFSG.D4Hex.sortKey a b c = sortKeyF a b c := by
  unfold CFSG.D4Hex.sortKey CFSG.D4Hex.lineKey sortKeyF
  simp only [Nat.min_def, Nat.max_def]
  by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ c <;> by_cases h3 : a ≤ c <;>
    simp only [h1, h2, h3, if_true, if_false] <;> (try split_ifs) <;> omega

theorem img_line {j l : ℕ} (hj : j < 8) (hl : l < 2457) :
    ∃ L < 2457, imgKey j l = keyF LTf L := by
  obtain ⟨p1, p2, p3⟩ := G4235.pts_parts l hl
  have hc := GD.okO0
  unfold orbOKRF at hc
  simp only [Bool.and_eq_true, MatL.allN_iff] at hc
  have h1 : (!(decide (819 ≤ 819 + l) && decide (819 + l < 3276)) ||
      (decide (Pst 0 (819 + l) < 2457) && Ot 0 (Pst 0 (819 + l)) == 819 + l)) = true :=
    hc.2 (819 + l) (by omega)
  have hi : (decide (819 ≤ 819 + l) && decide (819 + l < 3276)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [hi] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  obtain ⟨hp, ho⟩ := h1
  have ha := MatL.allN_iff.1 (MatL.allN_iff.1 GD.actO0 _ hp) j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
  obtain ⟨-, hs⟩ := ha
  rw [ho] at hs
  unfold actSOKF at hs
  rw [if_neg (by omega)] at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  obtain ⟨⟨hy1, hy2⟩, hkey⟩ := hs
  refine ⟨Ot 0 (Wt 0 (8 * Pst 0 (819 + l) + j)) - 819, by omega, ?_⟩
  rw [← hkey]
  have e : 819 + l - 819 = l := by omega
  rw [e]
  unfold imgKey gG
  simp only [if_pos hj]
  rw [lnPt0, lnPt1, lnPt2, perm_get (x := LTf (3 * l)) hj (by omega),
    perm_get (x := LTf (3 * l + 1)) hj (by omega), perm_get (x := LTf (3 * l + 2)) hj (by omega),
    sortKey_eq]

theorem line_parts : lineCheck = true := by
  have hb := LK.base
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hb
  unfold lineCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [lnPt0]
    exact Nat.eq_of_beq_eq_true GD.pt0K
  · rw [lnPt1]
    exact hb.1
  · rw [lnPt2]
    exact hb.2
  · rw [allLt_iff]
    intro l hl
    obtain ⟨p1, p2, p3⟩ := G4235.pts_parts l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    have hk : CFSG.D4Hex.lineKey (lnPt l 0) (lnPt l 1) (lnPt l 2) = keyF LTf l := by
      rw [lnPt0, lnPt1, lnPt2]
      rfl
    rw [hk, idx_key hl, lnPt0, lnPt1, lnPt2]
    exact ⟨⟨⟨p1, p2⟩, p3⟩, rfl⟩
  · rw [allLt_iff]
    intro j hj
    rw [allLt_iff]
    intro l hl
    obtain ⟨L, hL, hk⟩ := img_line hj hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [hk, idx_key hL, lnPt0, lnPt1, lnPt2]
    exact ⟨hL, rfl⟩

theorem flag_parts : baseFlagCheck = true := by
  have h := LK.flag
  unfold LK.flagF at h
  unfold baseFlagCheck fixesLine0
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨?_, ?_⟩
  · rw [allLt_iff]
    intro j hj
    rw [perm_get (x := 0) hj (by norm_num), perm_get (x := 1) hj (by norm_num),
      perm_get (x := 5) hj (by norm_num)]
    exact MatL.allN_iff.1 h.1 j hj
  · refine List.all_eq_true.2 fun j hm => ?_
    have hj : j < 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      omega
    rw [perm_get (x := 0) hj (by norm_num), perm_get (x := 1) hj (by norm_num),
      perm_get (x := 5) hj (by norm_num)]
    exact List.all_eq_true.1 h.2 j hm

open Certificates in
theorem c4234 : CFSG.D4Hex.linkCheck = true := by
  unfold linkCheck
  rw [link, line_parts, flag_parts]
  rfl

end CertificateChecks.KernelS63.L4234

end
