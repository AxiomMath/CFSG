module

public import Certificates.Kernel.Misc.TitsJ47.Facts
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import Certificates.Kernel.Sporadic.Tits.Order2264

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJ47

open CFSG.Quasithin.RuType.J47 CFSG.Quasithin.RuRank3
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsAction CertificateChecks.KernelMisc

theorem T_le : T ≤ titsA := by
  unfold T
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact titsD_le_titsA (titsT_mem_titsD (i := j.val) (by omega))

theorem t_mem : t ∈ titsA := by
  have e : t = titsGen 1 := by
    rw [titsGen, gen_eq (by norm_num)]
    rfl
  rw [e]
  exact titsGen_mem_titsA (by norm_num)

theorem mem_of_t {P : Nat} (hP : permC P = true) (hs : siftD (pcomp 1755 11 (mask 11) P (GI 1)) = true)
    (hc : permC (pcomp 1755 11 (mask 11) P (GI 1)) = true) :
    permOfArr 1755 (unpack 1755 11 P) ∈ titsA := by
  have h1 := mem_T hs hc
  rw [perm_mul hP TitsPi.permGI hc] at h1
  have hinv : permOfArr 1755 (unpack 1755 11 (GI 1)) = t⁻¹ :=
    (rep_of TitsPi.permGI).1.unique (rep_of (gperm 1 (by norm_num))).2
  rw [hinv] at h1
  have h2 := mul_mem (T_le h1) t_mem
  rwa [inv_mul_cancel_right] at h2

theorem mem_titsA {k : Nat} (hk : k < 7) : permOfArr 1755 (unpack 1755 11 (X k)) ∈ titsA := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec sifts k hk)
  rcases (by omega : k = 0 ∨ k = 5 ∨ (k ≠ 0 ∧ k ≠ 5)) with rfl | rfl | ⟨k0, k5⟩
  · exact mem_of_t (permX hk) h1 h2
  · exact mem_of_t (permX hk) h1 h2
  · have e : sx k = X k := by
      unfold sx
      have b0 : Nat.beq k 0 = false := by
        cases h : Nat.beq k 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) k0
      have b5 : Nat.beq k 5 = false := by
        cases h : Nat.beq k 5
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) k5
      rw [b0, b5]
    rw [e] at h1 h2
    exact T_le (mem_T h1 h2)

theorem inA {k : Nat} (hk : k < 7) : inTitsA (unpack 1755 11 (X k)) = true := by
  have hrep := (rep_of (permX hk)).1
  have hm := mem_titsA hk
  rw [← titsQA_original] at hm
  exact (siftA_iff_mem_ofArrays (n := 1755) (hn := by norm_num) (hk := by
      rw [titsAmbientArrs_size]; norm_num) (hb := by decide) (chunks := 4)
    titsChains_check.2.2.2.2.2.1 (by norm_num) titsChains_check.2.2.2.2.2.2.2.2.1 hrep).2 hm

theorem check1 : checkInTitsA = true := by
  unfold checkInTitsA dataArrs
  rw [a1_eq, f2_eq, e_eq, c_eq, b0_eq, aa_eq, ab_eq]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨⟨isInv_of (permX (by norm_num)), inA (by norm_num)⟩,
    ⟨isInv_of (permX (by norm_num)), inA (by norm_num)⟩,
    ⟨isInv_of (permX (by norm_num)), inA (by norm_num)⟩,
    ⟨isInv_of (permX (by norm_num)), inA (by norm_num)⟩,
    ⟨isInv_of (permX (by norm_num)), inA (by norm_num)⟩,
    ⟨isInv_of (permX (by norm_num)), inA (by norm_num)⟩,
    ⟨isInv_of (permX (by norm_num)), inA (by norm_num)⟩⟩

theorem c0 : C (X 0) := cX (by norm_num)
theorem c1 : C (X 1) := cX (by norm_num)
theorem c2 : C (X 2) := cX (by norm_num)
theorem c3 : C (X 3) := cX (by norm_num)
theorem c4 : C (X 4) := cX (by norm_num)
theorem c5 : C (X 5) := cX (by norm_num)
theorem c6 : C (X 6) := cX (by norm_num)

theorem check2 : checkLetterFix = true := by
  unfold checkLetterFix mulA
  rw [pi_eq, a1_eq, f2_eq, e_eq, j_eq, c_eq, b0_eq, aa_eq, ab_eq, idA_eq, mul_eq c2 c2,
    mul_eq c0 c2, eq_eq (cpc c2 c2) cid, lineFixed_eq cPi (by norm_num),
    lineFixed_eq c0 (by norm_num), lineFixed_eq c3 (by norm_num),
    lineMaps_eq (cpc c0 c2) (by norm_num) (by norm_num)]
  simp only [get_eq cPi, get_eq c0, get_eq c1, get_eq c2, get_eq c3, get_eq c4, get_eq c5,
    get_eq c6, get_eq cj', beqN]
  exact checks.1

theorem check3 : checkConjChain = true := by
  unfold checkConjChain
  rw [TitsCommon.z_eq, v1_eq, v2_eq, u_eq, zp_eq, jp_eq, t_eq, w1_eq, tp_eq]
  simp only [List.all_cons, List.all_nil, inS_eq cZ, inS_eq cv1, inS_eq cv2, inS_eq cu,
    inS_eq czp, inS_eq cjp, inS_eq ct, inS_eq cw1, inS_eq ctp]
  have h := checks.2.1
  simpa only [chainK, List.all_cons, List.all_nil] using h

theorem check4 : checkU = true := by
  unfold checkU mulA
  rw [u_eq, TitsCommon.z_eq, b0_eq, idA_eq, mul_eq cu cZ, mul_eq cZ cu, mul_eq cu c4,
    mul_eq (cpc cu c4) cu, (pow_eq c4 5).1, (pow_eq c4 4).1, eq_eq cu cZ,
    eq_eq (cpc cu cZ) (cpc cZ cu), eq_eq (pow_eq c4 5).2 cid, eq_eq c4 cid,
    eq_eq (cpc (cpc cu c4) cu) (pow_eq c4 4).2]
  exact checks.2.2.1

theorem normB_eq {k : Nat} (hk : k < 7) : normB (unpack 1755 11 (X k)) = normBK (X k) := by
  unfold normB normBK
  refine any_congr fun j _ => ?_
  rw [b0_eq, conj_eq hk c4, (pow_eq c4 j).1,
    eq_eq (show C (cj (X k) (X 4)) from cpc (cpc (cX hk) c4) (cXi hk)) (pow_eq c4 j).2]

theorem check5 : checkI = true := by
  have h := checks.2.2.2.1
  unfold iK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨i1, i2⟩, i3⟩, i4⟩, i5⟩, i6⟩, i7⟩ := h
  unfold checkI
  rw [aa_eq, ab_eq, normB_eq (by norm_num), normB_eq (by norm_num)]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, i4⟩, i5⟩, ?_⟩, ?_⟩
  · unfold mulA
    rw [mul_eq c5 c6, mul_eq c6 c5, eq_eq (cpc c5 c6) (cpc c6 c5)]
    exact i1
  · unfold mulA
    rw [u_eq, mul_eq c5 cu, mul_eq cu c5, eq_eq (cpc c5 cu) (cpc cu c5)]
    exact i2
  · unfold mulA
    rw [u_eq, mul_eq c6 cu, mul_eq cu c6, eq_eq (cpc c6 cu) (cpc cu c6)]
    exact i3
  · rw [allLt_iff']
    intro p hp
    rw [allLt_iff']
    intro q hq
    rw [prodI_eq, prodI_eq, eq_eq (cI hp) (cI hq), beqN]
    exact allN_spec (allN_spec i6 p hp) q hq
  · rw [allLt_iff']
    intro p hp
    unfold mulA
    rw [prodI_eq, idA_eq, TitsCommon.z_eq, u_eq, t_eq, mul_eq (cI hp) (cI hp),
      eq_eq (cpc (cI hp) (cI hp)) cid, eq_eq (cI hp) cid, eq_eq (cI hp) cZ, eq_eq (cI hp) cu,
      eq_eq (cI hp) ct]
    exact allN_spec i7 p hp

theorem check6 : checkFix = true := by
  unfold checkFix
  rw [u_eq, t_eq, fix_eq cu, fix_eq ct, beqN, beqN]
  exact checks.2.2.2.2.1

theorem check8 : checkY = true := by
  unfold checkY mulA
  rw [c_eq, tp_eq, zp_eq, jp_eq, idA_eq, (pow_eq c3 3).1, mul_eq c3 ctp, mul_eq ctp c3,
    conj_eq (k := 3) (by norm_num) czp, eq_eq (pow_eq c3 3).2 cid, eq_eq c3 cid,
    eq_eq (cpc c3 ctp) (cpc ctp c3), eq_eq (show C (cj (X 3) zpK) from cpc (cpc c3 czp) (cXi (by norm_num))) cjp]
  exact checks.2.2.2.2.2.2

theorem mem_modify {acc : Array (List Nat)} {i j x : Nat} {f : List Nat → List Nat}
    (hf : ∀ l, x ∈ l → x ∈ f l) (hi : i < acc.size) (h : x ∈ acc[i]!) :
    x ∈ (acc.modify j f)[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_modify]
  rw [getElem!_pos _ i hi] at h
  split
  · exact hf _ h
  · exact h

theorem mem_modify_self {acc : Array (List Nat)} {j v : Nat} (hj : j < acc.size) :
    v ∈ (acc.modify j fun l => l ++ [v])[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_modify, if_pos rfl]
  simp

theorem inner_fold (v : Nat) (g : Nat → Nat) : ∀ (ks : List Nat) (acc : Array (List Nat)),
    (∀ k ∈ ks, g k < acc.size) →
    (ks.foldl (fun a k => a.modify (g k) fun l => l ++ [v]) acc).size = acc.size ∧
    (∀ i < acc.size, ∀ x, x ∈ acc[i]! →
      x ∈ (ks.foldl (fun a k => a.modify (g k) fun l => l ++ [v]) acc)[i]!) ∧
    ∀ k ∈ ks, v ∈ (ks.foldl (fun a k => a.modify (g k) fun l => l ++ [v]) acc)[g k]!
  | [], acc, _ => ⟨rfl, fun _ _ _ h => h, fun _ h => absurd h List.not_mem_nil⟩
  | k :: ks, acc, hg => by
    rw [List.foldl_cons]
    have hs : (acc.modify (g k) fun l => l ++ [v]).size = acc.size := Array.size_modify
    obtain ⟨a1, a2, a3⟩ := inner_fold v g ks (acc.modify (g k) fun l => l ++ [v])
      (fun k' hk' => hs ▸ hg k' (List.mem_cons_of_mem _ hk'))
    refine ⟨a1.trans hs, fun i hi x hx => a2 i (hs ▸ hi) x
      (mem_modify (fun l hl => List.mem_append_left _ hl) hi hx), fun k' hk' => ?_⟩
    rcases List.mem_cons.1 hk' with rfl | hk'
    · exact a2 _ (hs ▸ hg _ List.mem_cons_self) _ (mem_modify_self (hg _ List.mem_cons_self))
    · exact a3 k' hk'

@[expose] def stepB (acc : Array (List Nat)) (v : Nat) : Array (List Nat) :=
  (List.range 3).foldl (fun acc' k => acc'.modify titsLinePtArr[3 * v + k]! fun l => l ++ [v]) acc

theorem lpA_lt {v k : Nat} (hv : v < 2925) (hk : k < 3) : titsLinePtArr[3 * v + k]! < 1755 := by
  rw [lp hv hk]
  exact lp_lt hv hk

theorem outer_fold : ∀ (vs : List Nat) (acc : Array (List Nat)), acc.size = 1755 →
    (∀ v ∈ vs, v < 2925) →
    (vs.foldl stepB acc).size = 1755 ∧
    (∀ i < 1755, ∀ x, x ∈ acc[i]! → x ∈ (vs.foldl stepB acc)[i]!) ∧
    ∀ v ∈ vs, ∀ k < 3, v ∈ (vs.foldl stepB acc)[titsLinePtArr[3 * v + k]!]!
  | [], acc, hs, _ => ⟨hs, fun _ _ _ h => h, fun _ h => absurd h List.not_mem_nil⟩
  | v :: vs, acc, hs, hv => by
    rw [List.foldl_cons]
    have hv0 := hv v List.mem_cons_self
    obtain ⟨i1, i2, i3⟩ := inner_fold v (fun k => titsLinePtArr[3 * v + k]!) (List.range 3) acc
      (fun k hk => hs ▸ lpA_lt hv0 (List.mem_range.1 hk))
    have hs1 : (stepB acc v).size = 1755 := i1.trans hs
    obtain ⟨o1, o2, o3⟩ := outer_fold vs (stepB acc v) hs1 (fun w hw => hv w (List.mem_cons_of_mem _ hw))
    refine ⟨o1, fun i hi x hx => o2 i hi x (i2 i (hs ▸ hi) x hx), fun w hw k hk => ?_⟩
    rcases List.mem_cons.1 hw with rfl | hw
    · exact o2 _ (lpA_lt hv0 hk) _ (i3 k (List.mem_range.2 hk))
    · exact o3 w hw k hk

theorem mem_buckets {v k : Nat} (hv : v < 2925) (hk : k < 3) :
    v ∈ ptLineBuckets[titsLinePtArr[3 * v + k]!]! :=
  (outer_fold (List.range 2925) (Array.replicate 1755 []) (by simp)
    (fun w hw => List.mem_range.1 hw)).2.2 v (List.mem_range.2 hv) k hk

theorem onLineK_spec {p v : Nat} (h : onLineK p v = true) : ∃ k < 3, lpK (3 * v + k) = p := by
  unfold onLineK at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact ⟨0, by norm_num, Nat.eq_of_beq_eq_true h⟩
  · exact ⟨1, by norm_num, Nat.eq_of_beq_eq_true h⟩
  · exact ⟨2, by norm_num, Nat.eq_of_beq_eq_true h⟩

theorem movedW_sound {q : Nat} (hm : movedW q = true) : ballMoved uArr q = true := by
  unfold movedW at hm
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨⟨⟨hv, hk⟩, hk'⟩, hw⟩, hon1⟩, hon2⟩, hmv⟩ := hm
  have hv' : pg 16 (mask 16) (J47W 0) q < 2925 := Nat.le_of_ble_eq_true hv
  have hk1 : pg 16 (mask 16) (J47W 1) q / 4 % 4 < 3 := Nat.le_of_ble_eq_true hk
  have hk2 : pg 16 (mask 16) (J47W 1) q % 4 < 3 := Nat.le_of_ble_eq_true hk'
  have hw' : pg 16 (mask 16) (J47W 1) q / 16 < 2925 := Nat.le_of_ble_eq_true hw
  unfold ballMoved
  rw [List.any_eq_true]
  refine ⟨pg 16 (mask 16) (J47W 0) q, ?_, ?_⟩
  · obtain ⟨k0, hk0, e⟩ := onLineK_spec hon1
    have h := mem_buckets hv' hk0
    rwa [lp hv' hk0, e] at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hv', by rw [onLine_eq _ hv']; exact hon1⟩, ?_⟩
    rw [List.any_eq_true]
    refine ⟨_, List.mem_range.2 hk1, ?_⟩
    rw [List.any_eq_true]
    refine ⟨pg 16 (mask 16) (J47W 1) q / 16, ?_, ?_⟩
    · obtain ⟨k1, hk1', e⟩ := onLineK_spec hon2
      have h := mem_buckets hw' hk1'
      rwa [lp hw' hk1', e, ← lp hv' hk1] at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨hw', by rw [lp hv' hk1, onLine_eq _ hw']; exact hon2⟩, ?_⟩
      rw [List.any_eq_true]
      refine ⟨_, List.mem_range.2 hk2, ?_⟩
      rw [lp hw' hk2, u_eq, get_eq cu, bne, beqN]
      exact hmv

theorem check7 : checkBall = true := by
  have h := checks.2.2.2.2.2.1
  unfold ballK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩ := h
  unfold checkBall
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [onLine_eq _ (by norm_num)]
    exact b1
  · rw [onLine_eq _ (by norm_num)]
    exact b2
  · rw [onLine_eq _ (by norm_num)]
    exact b3
  · rw [onLine_eq _ (by norm_num)]
    exact b4
  · unfold ballFixed
    unfold ballFixedK at b5
    rw [allLt_iff']
    intro v hv
    have h1 := allN_spec b5 v hv
    rw [onLine_eq _ hv]
    cases hq : onLineK 10 v
    · rfl
    · simp only [hq, Bool.not_true, Bool.false_or] at h1 ⊢
      rw [List.all_eq_true] at h1 ⊢
      intro k hk
      have h2 := h1 k hk
      rw [List.mem_range] at hk
      rw [allLt_iff']
      intro w hw
      have h3 := allN_spec h2 w hw
      rw [lp hv hk, onLine_eq _ hw]
      cases hq2 : onLineK (lpK (3 * v + k)) w
      · rfl
      · simp only [hq2, Bool.not_true, Bool.false_or] at h3 ⊢
        rw [all_congr fun k' hk' => by rw [lp hw hk', u_eq, get_eq cu, beqN]]
        exact h3
  · rw [allLt_iff']
    intro q hq
    have h1 := allN_spec b6 q hq
    rw [beqN]
    cases e : Nat.beq q 10
    · rw [e, Bool.false_or] at h1
      rw [Bool.false_or]
      exact movedW_sound h1
    · rfl
  · rw [allLt_iff']
    intro v hv
    have h1 := allN_spec b7 v hv
    rw [onLine_eq _ hv]
    cases hq : onLineK 0 v
    · rfl
    · simp only [hq, Bool.not_true, Bool.false_or] at h1 ⊢
      rw [List.all_eq_true] at h1 ⊢
      intro k hk
      have h2 := h1 k hk
      rw [List.mem_range] at hk
      rw [allLt_iff']
      intro w hw
      rw [lp hv hk, onLine_eq _ hw, onLine_eq _ hw, beqN, beqN]
      exact allN_spec h2 w hw
  · rw [allLt_iff']
    intro w hw
    rw [onLine_eq _ hw, onLine_eq _ hw, beqN]
    exact allN_spec b8 w hw

theorem checkAll_true : checkAll = true := by
  unfold checkAll
  rw [check1, check2, check3, check4, check5, check6, check7, check8]
  rfl

end CertificateChecks.KernelMisc.TitsJ47

end
