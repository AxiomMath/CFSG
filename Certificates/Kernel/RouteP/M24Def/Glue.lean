module

public import Certificates.Kernel.RouteP.M24Def.Checks
public import Certificates.Kernel.RouteP.M24Def.Checks64
public import Certificates.Kernel.RouteP.M24Def.Checks66
public import Certificates.Kernel.RouteP.M24.Bind
public import CFSG.Certificates.Kernel.RouteP.M24DefSound
public import CFSG.Certificates.Kernel.Common.ForallTree
meta import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelM24Def

open CFSG.KC.M24Def CFSG.KC.RouteP Certificates.RouteP.M24Defect CertificateChecks.KernelRouteP.M24

theorem ch450210twB : (treeTabL TTree.chars == (List.range 576).map fun q => decW (TW q)) = true := by
  decide +kernel

theorem ch450210cbB : (comboDataL TCombo.chars == (List.range 67).map fun r => decC (CB r)) = true := by
  decide +kernel

theorem ch450210sdB :
    (sDataL TBez.chars == (List.range 77).map fun k => (SD k % 2048, SD k / 2048)) = true := by
  decide +kernel

theorem ch450210tdB : (tDataL TBez.chars ==
    (List.range 67).map fun r => (List.range 7).map fun i => TD r / 2 ^ (11 * i) % 2048) = true := by
  decide +kernel

theorem tw_eq : treeTabL TTree.chars = (List.range 576).map fun q => decW (TW q) :=
  eq_of_beq ch450210twB

theorem cb_eq : comboDataL TCombo.chars = (List.range 67).map fun r => decC (CB r) :=
  eq_of_beq ch450210cbB

theorem sd_eq : sDataL TBez.chars = (List.range 77).map fun k => (SD k % 2048, SD k / 2048) :=
  eq_of_beq ch450210sdB

theorem td_eq : tDataL TBez.chars =
    (List.range 67).map fun r => (List.range 7).map fun i => TD r / 2 ^ (11 * i) % 2048 :=
  eq_of_beq ch450210tdB

theorem tab_eq : treeTab () = tabOf TW := by rw [treeTab_eq, tw_eq]; rfl

theorem combo_eq : comboData () = csOf CB := by rw [comboData_eq, cb_eq]; rfl

theorem s_eq : sData () = sOf SD := by rw [sData_eq, sd_eq]; rfl

theorem t_eq : tData () = tOf TD := by rw [tData_eq, td_eq]; rfl

theorem tree_all : ∀ q < 576, treeQ TW PA GQ FP LD LI q = true := by
  have hb : ∀ b < 9, ch450210tree b = true := by
    intro b hb
    interval_cases b
    · exact ch450210tree0
    · exact ch450210tree1
    · exact ch450210tree2
    · exact ch450210tree3
    · exact ch450210tree4
    · exact ch450210tree5
    · exact ch450210tree6
    · exact ch450210tree7
    · exact ch450210tree8
  intro q hq
  have h := allLt_eq_true.1 (hb (q / 64) (by omega)) (q % 64) (Nat.mod_lt _ (by omega))
  rwa [show Nat.add (Nat.mul 64 (q / 64)) (q % 64) = q from Nat.div_add_mod q 64] at h

theorem rel_words : ((List.range 7).map fun i => decR (RW i)) = relWords :=
  eq_of_beq ch450210relw

theorem ent_all {r : Nat} (hr : r < 67) : entriesOK (decC (CB r)) = true :=
  List.all_eq_true.1 ch450210ent _ (List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩)

theorem keyTab_foldl (L : List (Nat × Nat)) (A : Nat) :
    L.foldl (fun A c => A ^^^ (c.2 <<< (11 * c.1))) A =
      A ^^^ L.foldl (fun A c => A ^^^ (c.2 <<< (11 * c.1))) 0 := by
  induction L generalizing A with
  | nil => simp
  | cons c L ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (0 ^^^ _), Nat.zero_xor, Nat.xor_assoc]

theorem keyTab_append (A B : List (Nat × Nat)) : keyTab (A ++ B) = keyTab A ^^^ keyTab B := by
  unfold keyTab
  rw [List.foldl_append, keyTab_foldl]

noncomputable def kr (r lo len : Nat) : Nat :=
  keyTab (comboContribs (tabOf TW) (((decC (CB r)).drop lo).take len))

theorem kr_add (r lo a b : Nat) : kr r lo (a + b) = kr r lo a ^^^ kr r (lo + a) b := by
  unfold kr
  rw [List.take_add, comboContribs, List.flatMap_append, keyTab_append, List.drop_drop]
  rfl

theorem ln_zero (w P : Nat) : ln w P 0 = P % 2 ^ w := by
  unfold ln
  change (P >>> (w * 0)) &&& ((1 <<< w) - 1) = P % 2 ^ w
  rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.and_two_pow_sub_one_eq_mod P w

theorem kr_whole {r : Nat} : keyTab (comboContribs (tabOf TW) (decC (CB r))) =
    kr r 0 (CB r % 2 ^ 24) := by
  unfold kr
  rw [List.drop_zero, List.take_of_length_le (by simp [decC])]

theorem kr_run {r : Nat} (hr : r < 67) {lo len : Nat} (h : lo + len ≤ CB r % 2 ^ 24) :
    runE LD LI GQ FP RW (CB r) lo len 0 = kr r lo len := by
  rw [runE_eq TW PA GQ FP LD LI LM RW ch450210let tree_all rel_words (CB r) (ent_all hr) lo len 0 h,
    Nat.zero_xor]
  rfl

theorem kr_ck {r lo len j : Nat} (hr : r < 67) (h : lo + len ≤ CB r % 2 ^ 24)
    (hk : Nat.beq (runE LD LI GQ FP RW (CB r) lo len 0) (CK j) = true) : kr r lo len = CK j := by
  rw [← kr_run hr h]
  exact Nat.eq_of_beq_eq_true hk

#kc_forall_tree combo_low (fun r => ch450210c r = true) 64
  CertificateChecks.KernelM24Def.ch450210c

theorem key_low {r : Nat} (hr : r < 64) : keyTab (comboContribs (tabOf TW) (decC (CB r))) = 0 := by
  have h := combo_low r hr
  unfold ch450210c comboK at h
  rw [ln_zero] at h
  rw [kr_whole, ← kr_run (by omega) (by omega)]
  exact Nat.eq_of_beq_eq_true h

theorem kr_of {r n lo len j : Nat} (hr : r < 67) (hs : Nat.beq (ln 24 (CB r) 0) n = true)
    (hle : lo + len ≤ n) (hk : Nat.beq (runE LD LI GQ FP RW (CB r) lo len 0) (CK j) = true) :
    kr r lo len = CK j := by
  have hn : CB r % 2 ^ 24 = n := by rw [← ln_zero]; exact Nat.eq_of_beq_eq_true hs
  exact kr_ck hr (by omega) hk

theorem whole_of {r n : Nat} (hs : Nat.beq (ln 24 (CB r) 0) n = true) :
    keyTab (comboContribs (tabOf TW) (decC (CB r))) = kr r 0 n := by
  have hn : CB r % 2 ^ 24 = n := by rw [← ln_zero]; exact Nat.eq_of_beq_eq_true hs
  rw [kr_whole, hn]

theorem key_two {r n a b j1 j2 : Nat} (hr : r < 67) (hs : Nat.beq (ln 24 (CB r) 0) n = true)
    (hn : a + b = n)
    (h1 : Nat.beq (runE LD LI GQ FP RW (CB r) 0 a 0) (CK j1) = true)
    (h2 : Nat.beq (runE LD LI GQ FP RW (CB r) a b 0) (CK j2) = true)
    (hx : Nat.beq (Nat.xor (CK j1) (CK j2)) 0 = true) :
    keyTab (comboContribs (tabOf TW) (decC (CB r))) = 0 := by
  rw [whole_of hs, ← hn, kr_add, Nat.zero_add, kr_of hr hs (by omega) h1, kr_of hr hs (by omega) h2]
  exact Nat.eq_of_beq_eq_true hx

theorem key_four {r n a b c d l2 l3 j1 j2 j3 j4 : Nat} (hr : r < 67)
    (hs : Nat.beq (ln 24 (CB r) 0) n = true) (hn : a + b + c + d = n) (e2 : a + b = l2)
    (e3 : l2 + c = l3)
    (h1 : Nat.beq (runE LD LI GQ FP RW (CB r) 0 a 0) (CK j1) = true)
    (h2 : Nat.beq (runE LD LI GQ FP RW (CB r) a b 0) (CK j2) = true)
    (h3 : Nat.beq (runE LD LI GQ FP RW (CB r) l2 c 0) (CK j3) = true)
    (h4 : Nat.beq (runE LD LI GQ FP RW (CB r) l3 d 0) (CK j4) = true)
    (hx : Nat.beq (Nat.xor (Nat.xor (CK j1) (CK j2)) (Nat.xor (CK j3) (CK j4))) 0 = true) :
    keyTab (comboContribs (tabOf TW) (decC (CB r))) = 0 := by
  rw [whole_of hs, ← hn, kr_add, kr_add, kr_add]
  simp only [Nat.zero_add]
  rw [e2, e3, kr_of hr hs (by omega) h1, kr_of hr hs (by omega) h2, kr_of hr hs (by omega) h3,
    kr_of hr hs (by omega) h4, Nat.xor_assoc (CK j1 ^^^ CK j2)]
  exact Nat.eq_of_beq_eq_true hx

theorem key_five {r n a b c d f l2 l3 l4 j1 j2 j3 j4 j5 : Nat} (hr : r < 67)
    (hs : Nat.beq (ln 24 (CB r) 0) n = true) (hn : a + b + c + d + f = n) (e2 : a + b = l2)
    (e3 : l2 + c = l3) (e4 : l3 + d = l4)
    (h1 : Nat.beq (runE LD LI GQ FP RW (CB r) 0 a 0) (CK j1) = true)
    (h2 : Nat.beq (runE LD LI GQ FP RW (CB r) a b 0) (CK j2) = true)
    (h3 : Nat.beq (runE LD LI GQ FP RW (CB r) l2 c 0) (CK j3) = true)
    (h4 : Nat.beq (runE LD LI GQ FP RW (CB r) l3 d 0) (CK j4) = true)
    (h5 : Nat.beq (runE LD LI GQ FP RW (CB r) l4 f 0) (CK j5) = true)
    (hx : Nat.beq (Nat.xor (Nat.xor (CK j1) (CK j2))
      (Nat.xor (Nat.xor (CK j3) (CK j4)) (CK j5))) 0 = true) :
    keyTab (comboContribs (tabOf TW) (decC (CB r))) = 0 := by
  rw [whole_of hs, ← hn, kr_add, kr_add, kr_add, kr_add]
  simp only [Nat.zero_add]
  rw [e2, e3, e4, kr_of hr hs (by omega) h1, kr_of hr hs (by omega) h2,
    kr_of hr hs (by omega) h3, kr_of hr hs (by omega) h4, kr_of hr hs (by omega) h5,
    Nat.xor_assoc (CK j1 ^^^ CK j2 ^^^ CK j3) (CK j4) (CK j5),
    Nat.xor_assoc (CK j1 ^^^ CK j2) (CK j3) (CK j4 ^^^ CK j5), ← Nat.xor_assoc (CK j3) (CK j4)]
  exact Nat.eq_of_beq_eq_true hx

theorem key_64 : keyTab (comboContribs (tabOf TW) (decC (CB 64))) = 0 :=
  key_two (by decide) (Bool.and_eq_true_iff.1 ch450210s64).1 rfl ch450210k0 ch450210k1
    (Bool.and_eq_true_iff.1 ch450210s64).2

theorem key_65 : keyTab (comboContribs (tabOf TW) (decC (CB 65))) = 0 :=
  key_four (by decide) (Bool.and_eq_true_iff.1 ch450210s65).1 rfl rfl rfl ch450210k2 ch450210k3
    ch450210k4 ch450210k5 (Bool.and_eq_true_iff.1 ch450210s65).2

theorem key_66 : keyTab (comboContribs (tabOf TW) (decC (CB 66))) = 0 :=
  key_five (by decide) (Bool.and_eq_true_iff.1 ch450210s66).1 rfl rfl rfl rfl ch450210k6
    ch450210k7 ch450210k8 ch450210k9 ch450210k10 (Bool.and_eq_true_iff.1 ch450210s66).2

theorem key_all {r : Nat} (hr : r < 67) :
    keyTab (comboContribs (tabOf TW) (decC (CB r))) = 0 := by
  rcases (by omega : r < 64 ∨ r = 64 ∨ r = 65 ∨ r = 66) with h | rfl | rfl | rfl
  · exact key_low h
  · exact key_64
  · exact key_65
  · exact key_66

theorem checkAll_true : checkAll () = true := by
  unfold checkAll
  simp only [tab_eq, combo_eq, s_eq, t_eq, Bool.and_eq_true, beq_iff_eq]
  have ht := treeOK_of TW PA GQ FP LD LI LM ch450210let tree_all
  refine ⟨⟨⟨⟨⟨⟨ch450210letters, ?_⟩, ht.1⟩, ht.2.1⟩, by simp [csOf]⟩, ?_⟩, ?_⟩
  · exact relsOK_of RW LI LD LM ch450210let rel_words fun i hi =>
      allLt_eq_true.1 ch450210rel i hi
  · rw [List.all_eq_true]
    intro ents hm
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hm
    have hr' := List.mem_range.1 hr
    rw [Bool.and_eq_true]
    exact ⟨ent_all hr', bucketsZero_of_keyTab TW _ (ent_all hr') (key_all hr')⟩
  · exact bezoutOK_of TW PA GQ FP LD LI LM RW CB FS LA SD TD ch450210let tree_all rel_words
      ch450210ent (allLt_eq_true.1 ch450210fs)
      (fun i hi => Nat.eq_of_beq_eq_true (allLt_eq_true.1 ch450210lam i hi))
      (fun κ hκ => by simpa using allLt_eq_true.1 ch450210sd κ hκ)
      (fun κ hκ i hi => allLt_eq_true.1 (allLt_eq_true.1 ch450210bez κ hκ) i hi)

end CertificateChecks.KernelM24Def
