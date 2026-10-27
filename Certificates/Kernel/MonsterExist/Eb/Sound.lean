module

public import Certificates.Kernel.MonsterExist.Eb.Defs
public import CFSG.Monster.Existence.EbCheck
public import Certificates.Kernel.MonsterExist.ShortKey.Check

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.Eb

open CFSG.KC CFSG.KC.Loop CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster CFSG.Monster.B
  CFSG.Monster.Existence CFSG.Monster.B.TwoA.Census CertificateChecks.MonsterExist.ShortKey

theorem bXK_eq (x y : ℕ) : bXK x y = (bX x y).toNat := by
  unfold bXK bX
  change pairT x (y >>> 12) ^^^ pairT y (x >>> 12) = _
  rw [pairT_eq, pairT_eq, toNat_xor]

theorem beq_one_toNat (b : Bool) : Nat.beq b.toNat 1 = b := by cases b <;> rfl

theorem bNot_true {c : Bool} : bIf(c, false, true) = true ↔ c = false := by cases c <;> simp

theorem bNot_true' {t : Bool} : bIf(true, t, true) = t := rfl

theorem case1Range_iff (lo n : ℕ) : case1Range lo n = true ↔ ∀ k < n, case1Bucket (lo + k) = true :=
  natRec_and_iff (fun k => case1Bucket (Nat.add lo k)) n

theorem case1OK_of_buckets (h : ∀ a < 4096, case1Bucket a = true) :
    case1OK = true := by
  unfold case1OK
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨hv24, hvm⟩ := mem_shortPacked_iff_memK.1 hv
  have hvk := (memK_iff_mem bucket_ok hv24).1 hvm
  obtain ⟨a, ha, k, hk, rfl⟩ := mem_keyList_iff.1 hvk
  have hc := h a ha
  unfold case1Bucket at hc
  dsimp only at hc
  have hc2 := (natRec_and_iff _ _).1 hc k hk
  rw [laneW_slice SKV (offB (bkt a)) (cntB (bkt a)) k hk] at hc2
  change case1V (a + 4096 * dAt a k) = true at hc2
  generalize a + 4096 * dAt a k = v at hc2 hv24 ⊢
  have hA : ebCodeA = 782336 := rfl
  have hB : ebCodeB = 520192 := rfl
  have l1 : v ^^^ 782336 < 2 ^ 24 := Nat.xor_lt_two_pow hv24 (by norm_num)
  have l2 : v ^^^ 520192 < 2 ^ 24 := Nat.xor_lt_two_pow hv24 (by norm_num)
  have l3 : v ^^^ 782336 ^^^ 520192 < 2 ^ 24 := Nat.xor_lt_two_pow l1 (by norm_num)
  rw [hA, hB, ← memK_eq_isShortX l1, ← memK_eq_isShortX l2, ← memK_eq_isShortX l3]
  unfold case1V at hc2
  rw [bXK_eq, bXK_eq, beq_one_toNat, beq_one_toNat] at hc2
  revert hc2
  cases bX v 782336 <;> cases bX v 520192 <;> cases memK (v ^^^ 782336) <;>
    cases memK (v ^^^ 520192) <;> cases memK (v ^^^ 782336 ^^^ 520192) <;> decide

theorem allN_iff (P : ℕ → Bool) (n : ℕ) : allN P n = true ↔ ∀ k < n, P k = true :=
  natRec_and_iff P n


section Class0

theorem natCertOK_cls0 :
    natCertOK (Rep4371.Native.CosetEnum.act (imgs 1)) 24 (fun n => decide (n < 2 ^ 25)) (classEnc 0)
      (classCert 1 (classEnc 0)) = true :=
  (classCheck_spec (k := 0) (by norm_num)).1

theorem edgeRange_iff (lo n : ℕ) :
    edgeRange lo n = true ↔ ∀ i < n, ∀ k < 24, edgeAt (lo + i) k = true := by
  unfold edgeRange
  rw [allN_iff]
  exact forall_congr' fun i => imp_congr_right fun _ => allN_iff _ _

theorem treeOK_parts (ht : treeOK = true) :
    pt 0 = classEnc 0 ∧ ∀ i, 0 < i → i < 256 → treeAt i = true := by
  unfold treeOK at ht
  rw [bAnd_true, ShortKey.beq_true] at ht
  refine ⟨ht.1, fun i hi0 hi => ?_⟩
  have := (allN_iff _ _).1 ht.2 (i - 1) (by change i - 1 < 255; omega)
  rwa [show Nat.succ (i - 1) = i by omega] at this

theorem treeAt_spec {i : ℕ} (h : treeAt i = true) :
    ∃ par lab, par < i ∧ lab < 24 ∧ pt i = actK lab (pt par) := by
  unfold treeAt at h
  dsimp only at h
  rw [bAnd_true, bAnd_true, blt_true, blt_true, ShortKey.beq_true] at h
  exact ⟨_, _, h.1, h.2.1, h.2.2⟩

theorem edgeAt_spec {i k : ℕ} (h : edgeAt i k = true) : ∃ e < 256, pt e = actK k (pt i) := by
  unfold edgeAt at h
  dsimp only at h
  rw [bAnd_true, blt_true, ShortKey.beq_true] at h
  exact ⟨_, h.1, h.2⟩

theorem pts_mem (ht : treeOK = true) (he : ∀ i < 256, ∀ k < 24, edgeAt i k = true) :
    ∀ j < (classCert 1 (classEnc 0)).pts.size, ∃ i < 256, pt i = (classCert 1 (classEnc 0)).pts[j]! := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases j with _ | j
    · exact ⟨0, by norm_num, by rw [natCertOK_root natCertOK_cls0]; exact (treeOK_parts ht).1⟩
    · obtain ⟨hp, hl, e⟩ := natCertOK_tree natCertOK_cls0 (Nat.succ_pos j) hj
      obtain ⟨i, hi, hpi⟩ := ih _ hp (by omega)
      obtain ⟨e', he', hpe⟩ := edgeAt_spec (he i hi _ hl)
      refine ⟨e', he', ?_⟩
      rw [e, hpe, hpi]
      rfl

theorem pt_mem (ht : treeOK = true) :
    ∀ i < 256, ∃ j < (classCert 1 (classEnc 0)).pts.size, (classCert 1 (classEnc 0)).pts[j]! = pt i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | i
    · exact ⟨0, natCertOK_pos natCertOK_cls0, by rw [natCertOK_root natCertOK_cls0]; exact (treeOK_parts ht).1.symm⟩
    · obtain ⟨par, lab, hp, hl, e⟩ := treeAt_spec ((treeOK_parts ht).2 _ (Nat.succ_pos i) hi)
      obtain ⟨j, hj, hpj⟩ := ih par hp (by omega)
      obtain ⟨hj', e'⟩ := natCertOK_edge natCertOK_cls0 hj hl
      refine ⟨_, hj', ?_⟩
      rw [e', hpj, e]
      rfl

theorem mem_cls0_iff (ht : treeOK = true) (he : ∀ i < 256, ∀ k < 24, edgeAt i k = true) {n : ℕ} :
    n ∈ cls0 ↔ ∃ i < 256, pt i = n := by
  unfold cls0
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨i, hi, e⟩ := pts_mem ht he j hj
    refine ⟨i, hi, ?_⟩
    rw [e, getElem!_pos _ j hj]
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨j, hj, e⟩ := pt_mem ht i hi
    refine ⟨j, hj, ?_⟩
    rw [← e, getElem!_pos _ j hj]

theorem shortEnc_eq (n : ℕ) : shortEnc n = memK (n % 2 ^ 24) := by
  have e : packP (pauliDec n) = n % 2 ^ 24 := by
    unfold packP pauliDec
    simp only
    omega
  unfold shortEnc
  rw [e, memK_eq_isShortX (Nat.mod_lt _ (Nat.two_pow_pos 24))]

set_option exponentiation.threshold 8192 in
theorem boundOK_parts (hbd : boundOK = true) :
    CL < 2 ^ 6656 ∧ SH < 2 ^ 3120 ∧ (∀ i < 256, pt i < 2 ^ (26 - 1)) ∧
      ∀ j < 120, spt j < 2 ^ (26 - 1) := by
  unfold boundOK at hbd
  rw [bAnd_true, bAnd_true, bAnd_true, blt_true, blt_true] at hbd
  obtain ⟨h1, h2, h3, h4⟩ := hbd
  have h3 := (allN_iff _ _).1 h3
  have h4 := (allN_iff _ _).1 h4
  refine ⟨?_, ?_, fun i hi => blt_true.1 (h3 i hi), fun j hj => blt_true.1 (h4 j hj)⟩
  · rw [shl_one] at h1
    exact h1
  · rw [shl_one] at h2
    exact h2

theorem mem_CL_iff (hbd : boundOK = true) {d : ℕ} (hd : d < 2 ^ 25) :
    absentL 26 256 CL d = false ↔ ∃ i < 256, pt i = d := by
  obtain ⟨h1, -, h3, -⟩ := boundOK_parts hbd
  have h1' : CL < 2 ^ (26 * 256) := by rw [show (26 : ℕ) * 256 = 6656 from rfl]; exact h1
  rw [← Bool.not_eq_true, absentL_iff (W := 26) (by norm_num) h1' h3 hd]
  simp only [not_forall, not_not, exists_prop]
  rfl

theorem mem_SH_iff (hbd : boundOK = true) {d : ℕ} (hd : d < 2 ^ 25) :
    absentL 26 120 SH d = false ↔ ∃ j < 120, spt j = d := by
  obtain ⟨-, h2, -, h4⟩ := boundOK_parts hbd
  have h2' : SH < 2 ^ (26 * 120) := by rw [show (26 : ℕ) * 120 = 3120 from rfl]; exact h2
  rw [← Bool.not_eq_true, absentL_iff (W := 26) (by norm_num) h2' h4 hd]
  simp only [not_forall, not_not, exists_prop]
  rfl

theorem mem_sh_iff (ht : treeOK = true) (he : ∀ i < 256, ∀ k < 24, edgeAt i k = true)
    (hbd : boundOK = true)
    (h1 : ∀ j < 120, absentL 26 256 CL (spt j) = false ∧ memK (spt j % 2 ^ 24) = true)
    (h2 : ∀ i < 256, memK (pt i % 2 ^ 24) = true → absentL 26 120 SH (pt i) = false) {n : ℕ} :
    n ∈ cls0.filter shortEnc ↔ ∃ j < 120, spt j = n := by
  have hb := boundOK_parts hbd
  rw [List.mem_filter, mem_cls0_iff ht he]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hs⟩
    rw [shortEnc_eq] at hs
    exact (mem_SH_iff hbd (hb.2.2.1 i hi)).1 (h2 i hi hs)
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(mem_CL_iff hbd (hb.2.2.2 j hj)).1 (h1 j hj).1, ?_⟩
    rw [shortEnc_eq]
    exact (h1 j hj).2

theorem class0OK_of_checks (ht : treeOK = true) (he : ∀ i < 256, ∀ k < 24, edgeAt i k = true)
    (hbd : boundOK = true)
    (h1 : ∀ j < 120, absentL 26 256 CL (spt j) = false ∧ memK (spt j % 2 ^ 24) = true)
    (h2 : ∀ i < 256, memK (pt i % 2 ^ 24) = true → absentL 26 120 SH (pt i) = false)
    (hm : ∀ j < 120, ∀ j' < 120, absentL 26 120 SH (mulEnc (spt j) (spt j')) = true) :
    class0OK = true := by
  have hb := boundOK_parts hbd
  unfold class0OK
  simp only [List.all_eq_true, bne_iff_ne, ne_eq]
  intro n hn m hm' k hk e
  obtain ⟨j, hj, rfl⟩ := (mem_sh_iff ht he hbd h1 h2).1 hn
  obtain ⟨j', hj', rfl⟩ := (mem_sh_iff ht he hbd h1 h2).1 hm'
  obtain ⟨j'', hj'', rfl⟩ := (mem_sh_iff ht he hbd h1 h2).1 hk
  have := hm j hj j' hj'
  have h2' : SH < 2 ^ (26 * 120) := by rw [show (26 : ℕ) * 120 = 3120 from rfl]; exact hb.2.1
  rw [absentL_iff (W := 26) (by norm_num) h2' hb.2.2.2 (mulEnc_lt _ _)] at this
  exact this j'' hj'' e

end Class0

end CertificateChecks.MonsterExist.Eb

end
