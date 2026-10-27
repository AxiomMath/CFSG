module

public import Certificates.Kernel.J4Loc.SubsChk
public import Certificates.Kernel.J4Loc.TrioAsm
public import Certificates.Kernel.J4Q.C4024
public import CFSG.Certificates.Kernel.J4Loc.SubsSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTRankWitNative
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KD.J4Loc CFSG.KD.J4Q CFSG.KS.J4Loc CFSG.Sporadic.J4.QT
  CFSG.Quasithin.J4Loc CertificateChecks.KernelJ4Q

theorem ch4174_sb : decide (SB = subBases) = true := by quickRfl

theorem ch4174_lt : decide (∀ b ∈ subBases, ∀ v ∈ b, v < 2048) = true := by quickRfl

theorem neg4174_sb : (!decide (SB.set 3 [133, 778] = subBases)) = true := by quickRfl

theorem neg4174_lt : (!decide (∀ b ∈ subBases.set 4 [2048], ∀ v ∈ b, v < 2048)) = true := by
  quickRfl

theorem k4174_sb : SB = subBases := of_decide_eq_true ch4174_sb

theorem k4174_sub {b : ℕ} (hb : b < 22) :
    getN 0 SBK b = keyK (spanK (rowL SB b)) ∧ (spanK (rowL SB b)).Nodup ∧
      ∀ v ∈ rowL SB b, ∀ i < 4, actK (rowL mkKT i) v ∈ spanK (rowL SB b) ∧
        actK (rowL mkKIT i) v ∈ spanK (rowL SB b) :=
  subOK_spec (SUB.all b hb)

theorem k4174_kt {i : ℕ} (hi : i < 4) (c : ℕ) :
    actK (rowL mkKT i) c = actT (kTab i) c ∧ actK (rowL mkKIT i) c = actT (kInvTab i) c := by
  have h := (of_decide_eq_true lenK_chk) i (List.mem_range.2 hi)
  rw [rowL_eq, rowL_eq, kTab_eq hi, kInvTab_eq hi]
  exact ⟨actK_eq_actT (lenOK_iff h.1).1 c, actK_eq_actT (lenOK_iff h.2).1 c⟩

theorem k4174_rowL {b : ℕ} (hb : b < 22) : rowL SB b = subBases[b]'(by
    have : subBases.length = 22 := rfl
    omega) := by
  rw [rowL_eq, k4174_sb, List.getD_eq_getElem]

theorem k4174_mem_subs {B : List ℕ} (hB : B ∈ subs) : ∃ b < 22, B = spanS (rowL SB b) := by
  unfold subs at hB
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hB
  obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hc
  have hb' : b < 22 := by
    have : subBases.length = 22 := rfl
    omega
  exact ⟨b, hb', by rw [k4174_rowL hb']⟩

theorem k4174_spanS_mem {b : ℕ} (hb : b < 22) : spanS (rowL SB b) ∈ subs := by
  rw [k4174_rowL hb]
  exact List.mem_map_of_mem (List.getElem_mem _)

theorem k4174_bit {b : ℕ} (hb : b < 22) (x : ℕ) :
    (getN 0 SBK b).testBit x = true ↔ x ∈ spanS (rowL SB b) := by
  rw [mem_keyK_iff (k4174_sub hb).1, (spanS_spec _).1]

theorem k4174_subs_prop {B : List ℕ} (hB : B ∈ subs) :
    (∀ c ∈ B, c < 2048) ∧ B.Pairwise (· < ·) ∧ 0 ∈ B ∧ (∀ x ∈ B, ∀ y ∈ B, x ^^^ y ∈ B) ∧
      (∀ i < 4, ∀ c ∈ B, actT (kTab i) c ∈ B ∧ actT (kInvTab i) c ∈ B) := by
  obtain ⟨b, hb, rfl⟩ := k4174_mem_subs hB
  obtain ⟨hmem, -, hpw⟩ := spanS_spec (rowL SB b)
  obtain ⟨-, hnd, hinv⟩ := k4174_sub hb
  have hlt : ∀ v ∈ rowL SB b, v < 2 ^ 11 := by
    rw [k4174_rowL hb]
    exact (of_decide_eq_true ch4174_lt) _ (List.getElem_mem _)
  refine ⟨fun c hc => ?_, hpw hnd, (hmem 0).2 (zero_mem_spanK _), fun x hx y hy => ?_,
    fun i hi c hc => ?_⟩
  · exact spanK_induct (S := fun c => c < 2 ^ 11) (by decide)
      (fun x y hx hy => Nat.xor_lt_two_pow hx hy) _ hlt c ((hmem c).1 hc)
  · exact (hmem _).2 (xor_mem_spanK ((hmem x).1 hx) ((hmem y).1 hy))
  · have h1 := actT_mem_spanK (fun v hv => by
      rw [← (k4174_kt hi v).1]
      exact (hinv v hv i hi).1) c ((hmem c).1 hc)
    have h2 := actT_mem_spanK (fun v hv => by
      rw [← (k4174_kt hi v).2]
      exact (hinv v hv i hi).2) c ((hmem c).1 hc)
    exact ⟨(hmem _).2 h1, (hmem _).2 h2⟩

theorem k4174_subs_zero_mem : [0] ∈ subs := by
  have h : spanS (rowL SB 0) = [0] := by
    rw [k4174_rowL (by decide)]
    simp [spanS, srt, subBases]
  rw [← h]
  exact k4174_spanS_mem (by decide)

theorem k4174_subs_chain {B : List ℕ} (hB : B ∈ subs) {v : ℕ} (hv : v < 2048) (hvB : v ∉ B)
    (hfix : ∀ i < 4, (actT (kTab i) v ^^^ v) ∈ B) :
    ∃ B' ∈ subs, (∀ x ∈ B, x ∈ B') ∧ v ∈ B' ∧ ∀ y ∈ B', y ∈ B ∨ ∃ x ∈ B, y = x ^^^ v := by
  obtain ⟨b, hb, rfl⟩ := k4174_mem_subs hB
  have hmem := (spanS_spec (rowL SB b)).1
  have hnd := (k4174_sub hb).2.1
  have hvK : (getN 0 SBK b).testBit v = false := by
    cases h : (getN 0 SBK b).testBit v
    · rfl
    · exact absurd ((k4174_bit hb v).1 h) hvB
  obtain ⟨T, hT, hsub, hvT, hlen⟩ := chainOK_spec (CHN.all b hb) hv hvK
    (fun i hi => (k4174_bit hb _).2 (by rw [(k4174_kt hi v).1]; exact hfix i hi))
  have hmemT := (spanS_spec (rowL SB T)).1
  have hndT := (k4174_sub hT).2.1
  have hBT : ∀ x ∈ spanS (rowL SB b), x ∈ spanS (rowL SB T) := fun x hx =>
    (k4174_bit hT x).1 (hsub x ((k4174_bit hb x).2 hx))
  have hvT' : v ∈ spanS (rowL SB T) := (k4174_bit hT v).1 hvT
  refine ⟨_, k4174_spanS_mem hT, hBT, hvT', fun y hy => ?_⟩
  classical
  have hp := partner_eq (S := (spanK (rowL SB b)).toFinset) (S' := (spanK (rowL SB T)).toFinset)
    (v := v)
    (fun x hx y hy => List.mem_toFinset.2 (xor_mem_spanK (List.mem_toFinset.1 hx)
      (List.mem_toFinset.1 hy)))
    (fun h => hvB ((hmem v).2 (List.mem_toFinset.1 h)))
    (fun x hx => List.mem_toFinset.2 ((hmemT x).1 (hBT x ((hmem x).2 (List.mem_toFinset.1 hx)))))
    (List.mem_toFinset.2 ((hmemT v).1 hvT'))
    (fun x hx y hy => List.mem_toFinset.2 (xor_mem_spanK (List.mem_toFinset.1 hx)
      (List.mem_toFinset.1 hy)))
    (by
      rw [List.toFinset_card_of_nodup hndT, List.toFinset_card_of_nodup hnd, length_spanK,
        length_spanK, hlen, Nat.pow_succ]
      omega)
    y (List.mem_toFinset.2 ((hmemT y).1 hy))
  rcases hp with hp | ⟨x, hx, rfl⟩
  · exact Or.inl ((hmem y).2 (List.mem_toFinset.1 hp))
  · exact Or.inr ⟨x, (hmem x).2 (List.mem_toFinset.1 hx), rfl⟩

theorem k4174_tab {e : ℕ} (he : e < 1024) :
    seqT (pcSeq e) = tabK mkTLB e ∧ (tabK mkTLB e).length = 11 := by
  have h1 : tabK mkTLB e = mkTL.getD e [] := by
    rw [tabK_eq, ← tabAt_eq he]
    unfold tabAt
    rw [getL_eq, getBL_eq]
  rw [h1, tab_eq he]
  exact ⟨rfl, (lenOK_iff (of_decide_eq_true lenOK_chk _ (getD_mem_mkTL he))).1⟩

theorem k4174_xcnt {b : ℕ} (hb : b < 22) :
    xcnt (spanS (rowL SB b)) = cntK mkTLB INVS (rowL SB b) (getN 0 SBK b) := by
  have hmem := (spanS_spec (rowL SB b)).1
  have hKm : ∀ x, (getN 0 SBK b).testBit x = true ↔ x ∈ spanK (rowL SB b) :=
    mem_keyK_iff (k4174_sub hb).1
  have hinv := CFSG.KS.allN_spec (n := 1024)
    (f := fun e => eqB (bitB INVS e) (invK (tabK mkTLB e))) ch4174_inv
  unfold xcnt xset tabL
  rw [List.filter_map, List.length_map, cntK_eq]
  congr 1
  apply List.filter_congr
  intro e he
  have he' := List.mem_range.1 he
  obtain ⟨ht, hlen⟩ := k4174_tab he'
  rw [Function.comp_apply, ht, Bool.eq_iff_iff, andB_eq, eqB_spec (hinv e he')]
  simp only [Bool.and_eq_true, invK_iff hlen, inBK_iff hlen hKm, beq_iff_eq, List.all_eq_true,
    List.mem_range, List.contains_iff_mem, hmem, and_assoc]

theorem k4174_x_bound {B : List ℕ} (hB : B ∈ subs) (h16 : 16 ≤ B.length) :
    8 * xcnt B ≤ B.length ∧
      (8 * xcnt B = B.length → ∀ W ∈ TrioOct, (∀ w ∈ W, w ∈ B) → W = V0F) := by
  obtain ⟨b, hb, rfl⟩ := k4174_mem_subs hB
  have hlen := (spanS_spec (rowL SB b)).2.1
  rw [hlen] at h16 ⊢
  have hn : 4 ≤ (rowL SB b).length := by
    by_contra hc
    have : 2 ^ (rowL SB b).length ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨h1, h2⟩ := xOK_spec (XC.all b hb) hn
  rw [k4174_xcnt hb]
  refine ⟨h1, fun heq W hW hWB => ?_⟩
  rw [k4174_trio_eq] at hW
  obtain ⟨i, hi, rfl⟩ := hW
  have hx : ∀ x ∈ octL (fld 80 TRK i), (getN 0 SBK b).testBit x = true := fun x hx =>
    (k4174_bit hb x).2 (hWB x (List.mem_toFinset.2 hx))
  rw [onlyIn_spec (h2 heq) hi hx]
  exact k4174_V0

theorem k4174_above {B : List ℕ} (hB : B ∈ subs) (h3 : 3 ≤ B.length) {W : Finset ℕ}
    (hW : W ∈ TrioOct) (hsub : ∀ c ∈ B, c ∈ W) : W = V0F := by
  obtain ⟨b, hb, rfl⟩ := k4174_mem_subs hB
  have hlen := (spanS_spec (rowL SB b)).2.1
  rw [hlen] at h3
  have hn : 2 ≤ (rowL SB b).length := by
    by_contra hc
    have : 2 ^ (rowL SB b).length ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [k4174_trio_eq] at hW
  obtain ⟨i, hi, rfl⟩ := hW
  have hx : ∀ x, (getN 0 SBK b).testBit x = true → x ∈ octL (fld 80 TRK i) := fun x hx =>
    List.mem_toFinset.1 (hsub x ((k4174_bit hb x).1 hx))
  rw [onlyAbove_spec (aboveOK_spec (AB.all b hb) hn) hi hx]
  exact k4174_V0

end CertificateChecks.KernelJ4Loc

end
