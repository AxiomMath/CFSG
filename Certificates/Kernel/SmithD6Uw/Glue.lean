module

public import Certificates.Kernel.SmithD6Uw.Facts
public import Certificates.Kernel.SmithD6Uw.Model
public import Certificates.Kernel.SmithD6Stab.Glue
import all Certificates.Data.SmithD6Uw
import all Certificates.Kernel.SmithD6Uw.Facts

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Uw

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KD.SmithD6
  CFSG.GF2Type.SmithTypeE.DMod CertificateChecks.SmithD6Wt

theorem flatMap_lines_eq (F : ℕ → ℕ → ℕ) (x y : ℕ → ℕ) (c : ℕ → ℕ → Prop)
    [∀ a b, Decidable (c a b)] :
    ((List.range 6).flatMap fun a => (List.range 6).filterMap fun b =>
      if c a b then some (F (x a) (y b)) else none) =
    ((List.range 6).flatMap fun a => (List.range 6).filterMap fun b =>
      if c a b then some (x a, y b) else none).map (fun q => F q.1 q.2) := by
  rw [List.map_flatMap]
  congr 1
  funext a
  rw [List.map_filterMap]
  congr 1
  funext b
  split <;> rfl

theorem uw7Gens_toList : (uw7Gens ()).toList = uwGL.map fun q => lineOf q.1 q.2 := by
  unfold uw7Gens uw7FLines uw7LLines uwGL
  rw [Array.toList_append, List.toList_toArray, List.toList_toArray, List.map_append,
    flatMap_lines_eq lineOf fV fV (fun a b => a < b),
    flatMap_lines_eq lineOf eV fV (fun a b => (a != b) = true)]

theorem gen_facts {g : ℕ} (hg : g < 45) :
    (uwGL.getD g (0, 0)).1 < (uwGL.getD g (0, 0)).2 ∧
    (uwGL.getD g (0, 0)).2 < (uwGL.getD g (0, 0)).1 ^^^ (uwGL.getD g (0, 0)).2 ∧
    (uwGL.getD g (0, 0)).1 ^^^ (uwGL.getD g (0, 0)).2 < 4096 ∧
    lineTree.memB (4096 * (uwGL.getD g (0, 0)).1 + (uwGL.getD g (0, 0)).2) = true ∧
    rhoTOK (uwGL.getD g (0, 0)).1 (uwGL.getD g (0, 0)).2 (JU.uwT.getD g []) = true ∧
    liftT (JU.uwT.getD g []) 1 = 1 := by
  have hH := uwHeadK_ok
  simp only [uwHeadK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hH
  have h := hH.1.1.2 g hg
  simp only [uwGenK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h2, h3, h4, h1, h5, h6⟩

theorem uwGL_length : uwGL.length = 45 := by
  have hH := uwHeadK_ok
  simp only [uwHeadK, Bool.and_eq_true, beq_iff_eq] at hH
  exact hH.1.1.1

theorem uw7Gens_size : (uw7Gens ()).size = 45 := by
  rw [← Array.length_toList, uw7Gens_toList, List.length_map, uwGL_length]

theorem uw7Gens_get {g : ℕ} (hg : g < 45) :
    (uw7Gens ())[g]! = lineOf (uwGL.getD g (0, 0)).1 (uwGL.getD g (0, 0)).2 := by
  have hl : g < uwGL.length := by rw [uwGL_length]; exact hg
  rw [← Array.getElem!_toList, uw7Gens_toList, getElem!_pos _ g (by simpa using hl),
    List.getElem_map, getD_eq hl]

section Model

variable (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
  lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
include hL

theorem uw7Gens_line {g : ℕ} (hg : g < 45) :
    (uw7Gens ())[g]! < 365211 ∧ linePair (uw7Gens ())[g]! = uwGL.getD g (0, 0) := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := gen_facts hg
  rw [uw7Gens_get hg, lineOf_eq h1 h2]
  exact hL _ _ (by omega) (by omega) h4

end Model

theorem uwClsK_lt (s : ℕ) : uwClsK s < 4 := by
  unfold uwClsK
  cases Nat.beq s 1 <;> cases KT.memB (Nat.xor 1 s) wt64Tree <;>
    cases Nat.beq (Nat.land (Nat.shiftRight s 63) 1) 1 <;> decide

section Model

variable (hW : wtArr.toList = J.wtC.flatten)
include hW

theorem uw7Cls_eq {j : ℕ} (hj : j < 75735) : uw7Cls j = pkGet JU.uwK 2 j := by
  obtain ⟨-, hn64, hf64, hs64⟩ := wt64_facts
  obtain ⟨hp, hn, -, -⟩ := SmithD6Trees.wt_facts
  obtain ⟨h0l, h0⟩ := wt0
  have hjl : j < J.wtC.flatten.length := by rw [hn]; exact hj
  have hjl64 : j < J.wt64C.flatten.length := by rw [hn64]; exact hj
  have hsj := wtC_lt hjl
  have hmemj := List.getElem_mem hjl
  rw [uwCls_eq j hjl64, wt64_get hjl64]
  unfold uw7Cls adjW
  rw [wt_eq hW hjl, wt_eq hW h0l, h0, fB_one_left]
  by_cases hj0 : j = 0
  · subst hj0
    rw [h0, exC_one]
    rfl
  have hne := List.pairwise_iff_getElem.1 hp 0 j h0l hjl (Nat.pos_of_ne_zero hj0)
  rw [h0] at hne
  generalize J.wtC.flatten[j]'hjl = s at hsj hne hmemj ⊢
  have hne64 : Nat.beq (exC s) 1 = false := by
    refine Bool.eq_false_iff.2 fun h => Nat.ne_of_gt hne ?_
    exact exC_inj hsj (by norm_num) ((Nat.eq_of_beq_eq_true h).trans exC_one.symm)
  have hmem : KT.memB (Nat.xor 1 (exC s)) wt64Tree = decide (wtIdx (1 ^^^ s) < 75735) := by
    have hx : Nat.xor 1 (exC s) = exC (1 ^^^ s) := by
      rw [exC_xor, exC_one]
      rfl
    rw [hx, Bool.eq_iff_iff, memB_iff_mem hf64 hs64, decide_eq_true_iff, wtIdx_lt_iff hW,
      wt64_eq_map.1]
    constructor
    · intro h
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 h
      rwa [← exC_inj (wtC_lt_mem hy) (Nat.xor_lt_two_pow (by norm_num) hsj) hyx]
    · intro h
      exact List.mem_map_of_mem h
  have hbit : Nat.beq (Nat.land (Nat.shiftRight (exC s) 63) 1) 1 = s.testBit 31 := by
    rw [fld_one_eq, testBit_exC_63]
    cases s.testBit 31 <;> rfl
  have hb1 : (1 == s) = false := by
    rw [beq_eq_false_iff_ne]
    exact Nat.ne_of_lt hne
  unfold uwClsK
  rw [hne64, hmem, hbit, hb1, Bool.false_or, if_neg (by simpa using hj0)]
  cases decide (wtIdx (1 ^^^ s) < 75735) <;> cases s.testBit 31 <;> rfl

theorem uw7Reps_eq {c : ℕ} (hc : c < 4) : (uw7Reps ())[c]! = uwRep c := by
  have hH := uwHeadK_ok
  simp only [uwHeadK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at hH
  obtain ⟨hlt, hcls⟩ := hH.2 c hc
  have hn64 := wt64_facts.2.1
  have hfirst : ∀ a < uwRep c, (uw7Cls a == c) = false := by
    intro a ha
    have ha' : a < 75735 := Nat.lt_trans ha hlt
    rw [uw7Cls_eq hW ha', beq_eq_false_iff_ne]
    intro h
    have := uwFirst a (by rw [hn64]; exact ha')
    rw [h] at this
    omega
  have hf := CertificateChecks.SmithD6Stab.find?_range (p := fun a => uw7Cls a == c) hlt
    (by simp only [uw7Cls_eq hW hlt, hcls, beq_self_eq_true]) hfirst
  unfold uw7Reps
  rw [getElem!_pos]
  all_goals simp [hc, hf]

theorem uw7ChkCls_of_pinned : uw7ChkCls () = true := by
  have hH := uwHeadK_ok
  simp only [uwHeadK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at hH
  obtain ⟨n0, n1, n2, n3⟩ := uwCnt_vals
  have hcnt : ∀ c, ((List.range 75735).filter fun j => uw7Cls j == c).length = uwCnt c := by
    intro c
    rw [uwCnt_eq]
    congr 1
    apply List.filter_congr
    intro j hj
    rw [uw7Cls_eq hW (List.mem_range.1 hj)]
  have hsize : (uw7Reps ()).size = 4 := by
    unfold uw7Reps
    simp
  unfold uw7ChkCls
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨hsize, fun c hc => ?_⟩, fun c hc => ?_⟩
  · obtain ⟨hlt, hcls⟩ := hH.2 c hc
    rw [uw7Reps_eq hW hc, uw7Cls_eq hW hlt, hcls]
    exact ⟨hlt, rfl⟩
  · rw [hcnt]
    obtain rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
    · rw [n0]; rfl
    · rw [n1]; rfl
    · rw [n2]; rfl
    · rw [n3]; rfl

variable (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
  lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
include hL

theorem planeImg_gen {g a b : ℕ} (hg : g < 45) (ha : a < J.wtC.flatten.length)
    (hb : b < J.wtC.flatten.length)
    (h : liftT (JU.uwT.getD g []) (exC J.wtC.flatten[a]) = exC J.wtC.flatten[b]) :
    planeImg (uw7Gens ())[g]! a = b := by
  obtain ⟨-, -, -, -, hts, -⟩ := gen_facts hg
  obtain ⟨-, hl⟩ := uw7Gens_line hL hg
  have hy : J.wtC.flatten[b] < 2 ^ 32 := wtC_lt hb
  have hw : wtArr[a]! = J.wtC.flatten[a] := wt_eq hW ha
  unfold planeImg
  rw [hw, applyCols_of_liftT hl hts hy h, wtIdx_get hW hb]

theorem uw7ChkGens_of_pinned : uw7ChkGens () = true := by
  obtain ⟨h0l, h0⟩ := wt0
  unfold uw7ChkGens
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨uw7Gens_size, fun g hg => ?_⟩
  have hg45 : g < 45 := by rw [uw7Gens_size] at hg; exact hg
  rw [← getElem!_pos (uw7Gens ()) g hg]
  refine ⟨(uw7Gens_line hL hg45).1, ?_⟩
  obtain ⟨-, -, -, -, -, h1⟩ := gen_facts hg45
  exact planeImg_gen hW hL hg45 h0l h0l (by rw [h0, exC_one, h1])

theorem uw7Orb_of_pinned : ∀ v < 75735, Relation.ReflTransGen
    (fun a b => ∃ g < 45, uw7Cls a = uw7Cls b ∧ planeImg (uw7Gens ())[g]! a = b)
    ((uw7Reps ())[uw7Cls v]!) v := by
  obtain ⟨-, hn, -, -⟩ := SmithD6Trees.wt_facts
  have hn64 := wt64_facts.2.1
  intro v hv
  have hv64 : v < J.wt64C.flatten.length := by rw [hn64]; exact hv
  have hR := uwReach v hv64
  have hc : pkGet JU.uwK 2 v < 4 := by
    rw [uwCls_eq v hv64]
    exact uwClsK_lt _
  rw [uw7Cls_eq hW hv, uw7Reps_eq hW hc]
  refine Relation.ReflTransGen.mono (fun a b hab => ?_) _ _ hR
  have hab' : ∃ g < 45, pkGet JU.uwK 2 a = pkGet JU.uwK 2 b ∧
      ∃ (ha : a < J.wt64C.flatten.length) (hb : b < J.wt64C.flatten.length),
        liftT (JU.uwT.getD g []) (J.wt64C.flatten[a]'ha) = J.wt64C.flatten[b]'hb := hab
  obtain ⟨g, hg, hk, ha, hb, hl⟩ := hab'
  have ha' : a < 75735 := by rw [← hn64]; exact ha
  have hb' : b < 75735 := by rw [← hn64]; exact hb
  have ha32 : a < J.wtC.flatten.length := by rw [hn]; exact ha'
  have hb32 : b < J.wtC.flatten.length := by rw [hn]; exact hb'
  refine ⟨g, hg, by rw [uw7Cls_eq hW ha', uw7Cls_eq hW hb', hk], ?_⟩
  rw [wt64_get ha, wt64_get hb] at hl
  exact planeImg_gen hW hL hg ha32 hb32 hl

end Model

end CertificateChecks.SmithD6Uw

end
