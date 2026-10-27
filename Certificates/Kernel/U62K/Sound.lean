module

public import Certificates.Kernel.U62K.ChkDefs
public import Certificates.Kernel.Fi23T2.Glue
import Certificates.Kernel.U62K.Sl0
import Certificates.Kernel.U62K.Sl1
import Certificates.Kernel.U62K.Sl2
import Certificates.Kernel.U62K.Sl3
import Certificates.Kernel.U62K.Misc
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib

public section

set_option maxRecDepth 400000

#kon_join CFSG.KD.U62K.slAll CFSG.KD.U62K.slF 16
#kon_join CFSG.KD.U62K.clAll CFSG.KD.U62K.clF 3

namespace CertificateChecks.KernelU62K

open CFSG.KC.Enum CFSG.KD.U62K CFSG.KD.Fi23S CFSG.KS.Raw.Orb CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.Fi23 (J slvl sylG)
open CertificateChecks.KernelFi23T2 (eL pB)
open CFSG.KD.Fi23T2 (gL subP lenK)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def decW : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, c => if c = 0 then [] else (c % 64 - 1) :: decW n (c / 64)

section J


@[expose] noncomputable def wE (c : ℕ) : CFSG.Sporadic.Fi23.J := ((decW 16 c).map (pairG sylG)).prod

@[expose] def InT (x : CFSG.Sporadic.Fi23.J) : Prop := x ∈ slvl 0 ∧ idx 31671 x 14566 = 14566

theorem land63 (c : ℕ) : Nat.land c (nat_lit 63) = c % 64 := Nat.and_two_pow_sub_one_eq_mod c 6

theorem shr6 (c : ℕ) : Nat.shiftRight c (nat_lit 6) = c / 64 := Nat.shiftRight_eq_div_pow c 6

theorem vWn_succ {n c : ℕ} (hc : c ≠ 0) (h : vWn (n + 1) c = true) :
    c % 64 - 1 < 42 ∧ vWn n (c / 64) = true := by
  change bIf(Nat.beq c (nat_lit 0), true,
      bAnd(Nat.ble (nat_lit 1) (Nat.land c (nat_lit 63)),
        bAnd(Nat.ble (Nat.land c (nat_lit 63)) (nat_lit 42),
          vWn n (Nat.shiftRight c (nat_lit 6))))) = true at h
  rw [bIf_eq, if_neg (fun e => hc (Nat.eq_of_beq_eq_true e)), bAnd_eq, bAnd_eq,
    Bool.and_eq_true, Bool.and_eq_true, land63, shr6] at h
  have h2 : c % 64 ≤ 42 := Nat.ble_eq.mp h.2.1
  exact ⟨by omega, h.2.2⟩

theorem decW_succ {n c : ℕ} (hc : c ≠ 0) : decW (n + 1) c = (c % 64 - 1) :: decW n (c / 64) := by
  rw [decW, if_neg hc]

theorem vWn_zero {c : ℕ} (h : vWn 0 c = true) : c = 0 := Nat.eq_of_beq_eq_true h

theorem decW_mem_lt : ∀ {n c : ℕ}, vWn n c = true → ∀ l ∈ decW n c, l < 42
  | 0, c, _, l, hl => by simp [decW] at hl
  | n + 1, c, h, l, hl => by
    by_cases hc : c = 0
    · subst hc; simp [decW] at hl
    · rw [decW_succ hc] at hl
      obtain ⟨h1, h2⟩ := vWn_succ hc h
      rcases List.mem_cons.1 hl with rfl | hl
      · exact h1
      · exact decW_mem_lt h2 l hl

theorem idx_wPn : ∀ {n c : ℕ}, vWn n c = true → ∀ x < 31671,
    idx 31671 ((decW n c).map (pairG sylG)).prod x = wPn n c x
  | 0, c, h, x, _ => by
    rw [vWn_zero h]
    simp only [decW, List.map_nil, List.prod_nil, idx_one]
    rfl
  | n + 1, c, h, x, hx => by
    by_cases hc : c = 0
    · subst hc
      simp only [decW, if_true, List.map_nil, List.prod_nil, idx_one]
      rfl
    · obtain ⟨h1, h2⟩ := vWn_succ hc h
      rw [decW_succ hc, List.map_cons, List.prod_cons, idx_mul, idx_wPn h2 x hx]
      have hlt : wPn n (c / 64) x < 31671 := by rw [← idx_wPn h2 x hx]; exact idx_lt _ hx
      rw [KernelFi23T2.idx_lG h1 hlt]
      change _ = nIf(Nat.beq c (nat_lit 0), x,
        strictN (wPn n (Nat.shiftRight c (nat_lit 6)) x) fun y =>
          LS (Nat.sub (Nat.land c (nat_lit 63)) (nat_lit 1)) y)
      rw [nIf_eq, if_neg (fun e => hc (Nat.eq_of_beq_eq_true e)), strictN_eq, land63, shr6]
      rfl

theorem idx_wIn : ∀ {n c : ℕ}, vWn n c = true → ∀ x < 31671,
    idx 31671 ((decW n c).map (pairG sylG)).prod⁻¹ x = wIn n c x
  | 0, c, h, x, _ => by
    rw [vWn_zero h]
    simp only [decW, List.map_nil, List.prod_nil, inv_one, idx_one]
    rfl
  | n + 1, c, h, x, hx => by
    by_cases hc : c = 0
    · subst hc
      simp only [decW, if_true, List.map_nil, List.prod_nil, inv_one, idx_one]
      rfl
    · obtain ⟨h1, h2⟩ := vWn_succ hc h
      rw [decW_succ hc, List.map_cons, List.prod_cons, mul_inv_rev, idx_mul,
        KernelFi23T2.lG_inv, KernelFi23T2.idx_lG (KernelFi23T2.invL_lt42 h1) hx]
      have hlt := KernelFi23T2.LS_lt' (KernelFi23T2.invL_lt42 h1) hx
      rw [idx_wIn h2 _ hlt]
      change _ = nIf(Nat.beq c (nat_lit 0), x,
        strictN (LS (Nat.xor (Nat.sub (Nat.land c (nat_lit 63)) (nat_lit 1)) (nat_lit 1)) x)
          fun y => wIn n (Nat.shiftRight c (nat_lit 6)) y)
      rw [nIf_eq, if_neg (fun e => hc (Nat.eq_of_beq_eq_true e)), strictN_eq, land63, shr6]
      rfl

theorem idx_wE {c : ℕ} (hc : vW c = true) {x : ℕ} (hx : x < 31671) :
    idx 31671 (wE c) x = wP c x := idx_wPn hc x hx

theorem idx_wE_inv {c : ℕ} (hc : vW c = true) {x : ℕ} (hx : x < 31671) :
    idx 31671 (wE c)⁻¹ x = wI c x := idx_wIn hc x hx

theorem wE_mem {c : ℕ} (hc : vW c = true) : wE c ∈ slvl 0 := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg
  exact KernelFi23T2.lG_mem (decW_mem_lt hc l hl)

theorem qq_eq : qq = 14566 := rfl

theorem digit_ne {a r : ℕ} (ha1 : 1 ≤ a) : a + 64 * r ≠ 0 := by omega

theorem digit_mod {a r : ℕ} (ha : a < 64) : (a + 64 * r) % 64 = a := by omega

theorem digit_div {a r : ℕ} (ha : a < 64) : (a + 64 * r) / 64 = r := by omega

theorem decW_digit {n a r : ℕ} (ha1 : 1 ≤ a) (ha : a < 64) :
    decW (n + 1) (a + 64 * r) = (a - 1) :: decW n r := by
  rw [decW_succ (digit_ne ha1), digit_mod ha, digit_div ha]

theorem decW_zero {n : ℕ} : decW n 0 = [] := by
  cases n <;> simp [decW]

theorem wPn_digit {n a r x : ℕ} (ha1 : 1 ≤ a) (ha : a < 64) :
    wPn (n + 1) (a + 64 * r) x = LS (a - 1) (wPn n r x) := by
  change nIf(Nat.beq (a + 64 * r) (nat_lit 0), x,
    strictN (wPn n (Nat.shiftRight (a + 64 * r) (nat_lit 6)) x) fun y =>
      LS (Nat.sub (Nat.land (a + 64 * r) (nat_lit 63)) (nat_lit 1)) y) = _
  rw [nIf_eq, if_neg (fun e => digit_ne ha1 (Nat.eq_of_beq_eq_true e)), strictN_eq, land63, shr6,
    digit_mod ha, digit_div ha]
  rfl

theorem wPn_zero {n x : ℕ} : wPn n 0 x = x := by
  cases n <;> rfl

theorem vWn_digit {n a r : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ 42) :
    vWn (n + 1) (a + 64 * r) = vWn n r := by
  change bIf(Nat.beq (a + 64 * r) (nat_lit 0), true,
      bAnd(Nat.ble (nat_lit 1) (Nat.land (a + 64 * r) (nat_lit 63)),
        bAnd(Nat.ble (Nat.land (a + 64 * r) (nat_lit 63)) (nat_lit 42),
          vWn n (Nat.shiftRight (a + 64 * r) (nat_lit 6))))) = _
  rw [bIf_eq, if_neg (fun e => digit_ne ha1 (Nat.eq_of_beq_eq_true e)), land63, shr6,
    digit_mod (by omega), digit_div (by omega), bAnd_eq, bAnd_eq,
    Nat.ble_eq_true_of_le ha1, Nat.ble_eq_true_of_le ha, Bool.true_and, Bool.true_and]

theorem vWn_zero' {n : ℕ} : vWn n 0 = true := by
  cases n <;> rfl

theorem sw_spec {u : ℕ} (hu : u < 84) : vW (sw u) = true ∧
    wE (sw u) = (if u < 42 then
      (if idx 31671 (pairG sylG u) 14566 = 14566 then pairG sylG u
        else pairG sylG u * (pairG sylG 2)⁻¹)
    else (if idx 31671 (pairG sylG 2 * pairG sylG (u - 42)) 14566 = 14566 then
        pairG sylG 2 * pairG sylG (u - 42)
      else pairG sylG 2 * pairG sylG (u - 42) * (pairG sylG 2)⁻¹)) := by
  have l3 : pairG sylG 3 = (pairG sylG 2)⁻¹ := by rw [KernelFi23T2.lG_inv]; rfl
  have hq : (14566 : ℕ) < 31671 := by norm_num
  by_cases h42 : u < 42
  · have hb : Nat.blt u (nat_lit 42) = true := Nat.blt_eq.mpr h42
    have e0 : sw u = if wP (u + 1) 14566 = 14566 then u + 1 else u + 1 + 256 := by
      unfold sw
      simp only [strictN_eq, nIf_eq, hb, if_true, qq_eq, Nat.beq_eq_true_eq, Nat.succ_eq_add_one]
      rw [show Nat.mod u 42 = u from Nat.mod_eq_of_lt h42]
      have k : Nat.add (u + 1) (Nat.shiftLeft 4 6) = u + 1 + 256 := rfl
      rw [k]
      simp only [Nat.beq_eq]
    have hw : wP (u + 1) 14566 = LS u 14566 := by
      rw [show u + 1 = (u + 1) + 64 * 0 by omega]
      unfold wP
      rw [wPn_digit (n := 15) (by omega) (by omega), wPn_zero]
      congr 1
    rw [hw] at e0
    rw [if_pos h42, KernelFi23T2.idx_lG h42 hq]
    by_cases hf : LS u 14566 = 14566
    · rw [if_pos hf] at e0
      rw [e0, if_pos hf, show u + 1 = (u + 1) + 64 * 0 by omega]
      refine ⟨?_, ?_⟩
      · unfold vW
        rw [vWn_digit (n := 15) (by omega) (by omega), vWn_zero']
      · unfold wE
        rw [decW_digit (n := 15) (by omega) (by omega), decW_zero]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          Nat.add_sub_cancel]
    · rw [if_neg hf] at e0
      rw [e0, if_neg hf, show u + 1 + 256 = (u + 1) + 64 * (4 + 64 * 0) by omega]
      refine ⟨?_, ?_⟩
      · unfold vW
        rw [vWn_digit (n := 15) (by omega) (by omega), vWn_digit (n := 14) (by omega) (by omega),
          vWn_zero']
      · unfold wE
        rw [decW_digit (n := 15) (by omega) (by omega), decW_digit (n := 14) (by omega) (by omega),
          decW_zero]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          Nat.add_sub_cancel]
        rw [show 4 - 1 = 3 from rfl, l3]
  · have hb : Nat.blt u (nat_lit 42) = false := by
      cases h : Nat.blt u (nat_lit 42)
      · rfl
      · exact absurd (Nat.blt_eq.mp h) h42
    have hl : u % 42 = u - 42 := by omega
    have hl42 : u - 42 < 42 := by omega
    have e0 : sw u = if wP (3 + 64 * ((u - 42 + 1) + 64 * 0)) 14566 = 14566 then
        3 + 64 * ((u - 42 + 1) + 64 * 0) else 3 + 64 * ((u - 42 + 1) + 64 * (4 + 64 * 0)) := by
      unfold sw
      simp only [strictN_eq, nIf_eq, hb, Bool.false_eq_true, if_false, qq_eq,
        Nat.beq_eq_true_eq, Nat.succ_eq_add_one]
      have k1 : Nat.add 3 (Nat.shiftLeft (Nat.mod u 42 + 1) 6) =
          3 + 64 * ((u - 42 + 1) + 64 * 0) := by
        change 3 + (u % 42 + 1) <<< 6 = _
        rw [Nat.shiftLeft_eq, hl]
        ring
      have k2 : Nat.add (3 + 64 * ((u - 42 + 1) + 64 * 0)) (Nat.shiftLeft 4 12) =
          3 + 64 * ((u - 42 + 1) + 64 * (4 + 64 * 0)) := by
        change _ + 4 <<< 12 = _
        rw [Nat.shiftLeft_eq]
        ring
      rw [k1, k2]
      simp only [Nat.beq_eq]
    have hw : wP (3 + 64 * ((u - 42 + 1) + 64 * 0)) 14566 = LS 2 (LS (u - 42) 14566) := by
      unfold wP
      rw [wPn_digit (n := 15) (by omega) (by omega), wPn_digit (n := 14) (by omega) (by omega),
        wPn_zero]
      rfl
    have hidx : idx 31671 (pairG sylG 2 * pairG sylG (u - 42)) 14566 = LS 2 (LS (u - 42) 14566) := by
      rw [idx_mul, KernelFi23T2.idx_lG hl42 hq,
        KernelFi23T2.idx_lG (by norm_num) (KernelFi23T2.LS_lt' hl42 hq)]
    rw [hw] at e0
    rw [if_neg h42, hidx]
    by_cases hf : LS 2 (LS (u - 42) 14566) = 14566
    · rw [if_pos hf] at e0
      rw [e0, if_pos hf]
      refine ⟨?_, ?_⟩
      · unfold vW
        rw [vWn_digit (n := 15) (by omega) (by omega), vWn_digit (n := 14) (by omega) (by omega),
          vWn_zero']
      · unfold wE
        rw [decW_digit (n := 15) (by omega) (by omega), decW_digit (n := 14) (by omega) (by omega),
          decW_zero]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          Nat.add_sub_cancel]
    · rw [if_neg hf] at e0
      rw [e0, if_neg hf]
      refine ⟨?_, ?_⟩
      · unfold vW
        rw [vWn_digit (n := 15) (by omega) (by omega), vWn_digit (n := 14) (by omega) (by omega),
          vWn_digit (n := 13) (by omega) (by omega), vWn_zero']
      · unfold wE
        rw [decW_digit (n := 15) (by omega) (by omega), decW_digit (n := 14) (by omega) (by omega),
          decW_digit (n := 13) (by omega) (by omega), decW_zero]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          Nat.add_sub_cancel]
        rw [show 4 - 1 = 3 from rfl, show 3 - 1 = 2 from rfl, l3, mul_assoc]

theorem allL_spec {f : ℕ → Bool} : ∀ {l : List ℕ}, allL f l = true → ∀ b ∈ l, f b = true
  | [], _, b, hb => absurd hb List.not_mem_nil
  | c :: l, h, b, hb => by
    change bAnd(f c, allL f l) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact allL_spec h.2 b hb

theorem incK_spec {f : ℕ → ℕ} : ∀ {l : List ℕ} {a : ℕ}, incK f a l = true →
    (∀ b ∈ l, a < f b) ∧ l.Pairwise fun x y => f x < f y
  | [], _, _ => ⟨fun b hb => absurd hb List.not_mem_nil, List.Pairwise.nil⟩
  | b :: t, a, h => by
    change strictB (f b) (fun k => bAnd(Nat.blt a k, incK f k t)) = true at h
    rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
    have hab := Nat.blt_eq.mp h.1
    obtain ⟨h1, h2⟩ := incK_spec h.2
    refine ⟨fun c hc => ?_, List.Pairwise.cons h1 h2⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact hab.trans (h1 c hc)

theorem incK_nodup {f : ℕ → ℕ} {l : List ℕ} {a : ℕ} (h : incK f a l = true) :
    (l.map f).Nodup :=
  List.pairwise_map.2 ((incK_spec h).2.imp fun hxy => Nat.ne_of_lt hxy)

theorem invQ_spec {i : ℕ} (h : invQ i = true) :
    i < 262144 ∧ gL i 14566 = 14566 ∧ ∀ p < 6, gL i (gL i p) = p := by
  unfold invQ at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2.1,
    fun p hp => Nat.eq_of_beq_eq_true (allN_iff.1 h.2.2 p hp)⟩

theorem inT_eL {i : ℕ} (hi : i < 262144) (hq : gL i 14566 = 14566) : InT (eL i) :=
  ⟨KernelFi23T2.eL_mem i hi, by rw [KernelFi23T2.idx_e hi (by norm_num)]; exact hq⟩

theorem eL_sq {i : ℕ} (hi : i < 262144) (h : ∀ p < 6, gL i (gL i p) = p) : eL i * eL i = 1 :=
  KernelFi23T2.eq_six fun t ht => by
    rw [idx_mul, KernelFi23T2.idx_e hi (KernelFi23T2.lt_of_six ht),
      KernelFi23T2.idx_e hi (KernelFi23T2.gL_lt hi (KernelFi23T2.lt_of_six ht)), idx_one]
    exact h t ht

theorem pwK_spec : ∀ {l : List ℕ}, pwK l = true → l.Pairwise fun a b => commK a b = true
  | [], _ => List.Pairwise.nil
  | a :: t, h => by
    change bAnd(allL (commK a) t, pwK t) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    exact List.Pairwise.cons (allL_spec h.1) (pwK_spec h.2)

theorem eL_comm {a b : ℕ} (ha : a < 262144) (hb : b < 262144) (h : commK a b = true) :
    eL a * eL b = eL b * eL a :=
  KernelFi23T2.eq_six fun t ht => by
    have ht' := KernelFi23T2.lt_of_six ht
    rw [idx_mul, idx_mul, KernelFi23T2.idx_e hb ht', KernelFi23T2.idx_e ha ht',
      KernelFi23T2.idx_e ha (KernelFi23T2.gL_lt hb ht'),
      KernelFi23T2.idx_e hb (KernelFi23T2.gL_lt ha ht')]
    exact Nat.eq_of_beq_eq_true (allN_iff.1 h t ht)

theorem bK_parts : D.B.length = 11 ∧ (∀ b ∈ D.B, invQ b = true) ∧
    D.B.Pairwise fun a b => commK a b = true := by
  have h := bOK
  unfold bK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, KernelFi23T2.lenK_eq] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, allL_spec h.2.1, pwK_spec h.2.2⟩

theorem B_lt : ∀ a ∈ D.B, a < 262144 := fun a ha => (invQ_spec (bK_parts.2.1 a ha)).1

theorem basis_spec : D.B.length = 11 ∧ (∀ b ∈ D.B, b < 262144 ∧ InT (eL b) ∧ eL b * eL b = 1) ∧
    ∀ a ∈ D.B, ∀ b ∈ D.B, eL a * eL b = eL b * eL a := by
  obtain ⟨hlen, hinv, hpw⟩ := bK_parts
  refine ⟨hlen, fun b hb => ?_, fun a ha b hb => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := invQ_spec (hinv b hb)
    exact ⟨h1, inT_eL h1 h2, eL_sq h1 h3⟩
  · by_cases e : a = b
    · rw [e]
    · rcases KernelFi23T2.pw_mem hpw ha hb e with h | h
      · exact eL_comm (B_lt a ha) (B_lt b hb) h
      · exact (eL_comm (B_lt b hb) (B_lt a ha) h).symm

theorem K_parts : D.K.length = 2048 ∧ (∀ m ∈ D.K, m < 2048) ∧ (D.K.map subKey).Nodup := by
  have h := kOK
  unfold kK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, KernelFi23T2.lenK_eq] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, fun m hm => Nat.blt_eq.mp (allL_spec h.2.1 m hm),
    incK_nodup h.2.2⟩

theorem masks_spec : ∃ f : Fin 2048 → ℕ, (∀ s, f s < 2048) ∧
    Function.Injective fun s => pB D.B (f s) := by
  obtain ⟨hlen, hlt, hnd⟩ := K_parts
  refine ⟨fun s => D.K[s.val]'(by rw [hlen]; exact s.isLt),
    fun s => hlt _ (List.getElem_mem _), fun s t hst => ?_⟩
  have k0 := congrArg (fun y => idx 31671 y 0) hst
  have k2 := congrArg (fun y => idx 31671 y 2) hst
  simp only at k0 k2
  rw [KernelFi23T2.idx_pB B_lt _ _ (by norm_num), KernelFi23T2.idx_pB B_lt _ _ (by norm_num)] at k0 k2
  have hk : subKey (D.K[s.val]'(by rw [hlen]; exact s.isLt)) =
      subKey (D.K[t.val]'(by rw [hlen]; exact t.isLt)) := by
    unfold subKey
    rw [k0, k2]
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (i := s.val) (j := t.val)
    (hi := by rw [List.length_map, hlen]; exact s.isLt)
    (hj := by rw [List.length_map, hlen]; exact t.isLt)).1
    (by rw [List.getElem_map, List.getElem_map]; exact hk))

theorem okW_spec {c : ℕ} (h : okW c = true) : vW c = true ∧ wP c 14566 = 14566 := by
  unfold okW at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem inT_wE {c : ℕ} (h : okW c = true) : InT (wE c) :=
  ⟨wE_mem (okW_spec h).1, by rw [idx_wE (okW_spec h).1 (by norm_num)]; exact (okW_spec h).2⟩

theorem idx_cj {c i p : ℕ} (hc : vW c = true) (hi : i < 262144) (hp : p < 31671) :
    idx 31671 (wE c * eL i * (wE c)⁻¹) p = cj c i p := by
  have h1 : wI c p < 31671 := by rw [← idx_wE_inv hc hp]; exact idx_lt _ hp
  have h2 := KernelFi23T2.gL_lt hi h1
  rw [idx_mul, idx_mul, idx_wE_inv hc hp, KernelFi23T2.idx_e hi h1, idx_wE hc h2]
  rfl

theorem idx_cjI {c i p : ℕ} (hc : vW c = true) (hi : i < 262144) (hp : p < 31671) :
    idx 31671 ((wE c)⁻¹ * eL i * (wE c)⁻¹⁻¹) p = cjI c i p := by
  have h1 : wP c p < 31671 := by rw [← idx_wE hc hp]; exact idx_lt _ hp
  have h2 := KernelFi23T2.gL_lt hi h1
  rw [inv_inv, idx_mul, idx_mul, idx_wE hc hp, KernelFi23T2.idx_e hi h1, idx_wE_inv hc h2]
  rfl

theorem inE_spec {i m : ℕ} (h : inE i m = true) : m < 2048 ∧ ∀ p < 6, gL i p = subP D.B m p := by
  unfold inE at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, fun p hp => Nat.eq_of_beq_eq_true (allN_iff.1 h.2 p hp)⟩

theorem wOK_spec {e : List ℕ} (h : wOK e = true) :
    (∃ m, e = [CFSG.KD.Fi23T2.hd e, 0, m] ∧ inE (CFSG.KD.Fi23T2.hd e) m = true) ∨
      ∃ cs : List ℕ, e = CFSG.KD.Fi23T2.hd e :: 1 :: cs ∧ cs.length = 9 ∧
        (∀ c ∈ cs, okW c = true) ∧ (cs.map (kyW (CFSG.KD.Fi23T2.hd e))).Nodup := by
  match e, h with
  | i :: tag :: us, h =>
    change bIf(Nat.beq tag (nat_lit 0),
        List.rec (motive := fun _ => Bool) false
          (fun m r _ => bAnd(Nat.beq (lenK r) (nat_lit 0), inE i m)) us,
        bAnd(Nat.beq tag (nat_lit 1), bAnd(Nat.beq (lenK us) (nat_lit 9),
          bAnd(allL okW us, incK (kyW i) (nat_lit 0) us)))) = true at h
    change (∃ m, i :: tag :: us = [i, 0, m] ∧ inE i m = true) ∨
      ∃ cs : List ℕ, i :: tag :: us = i :: 1 :: cs ∧ cs.length = 9 ∧
        (∀ c ∈ cs, okW c = true) ∧ (cs.map (kyW i)).Nodup
    rw [bIf_eq] at h
    split_ifs at h with h0
    · left
      have ht : tag = 0 := Nat.eq_of_beq_eq_true h0
      match us, h with
      | m :: r, h =>
        change bAnd(Nat.beq (lenK r) (nat_lit 0), inE i m) = true at h
        rw [bAnd_eq, Bool.and_eq_true, KernelFi23T2.lenK_eq] at h
        have hr : r = [] := List.eq_nil_of_length_eq_zero (Nat.eq_of_beq_eq_true h.1)
        exact ⟨m, by rw [ht, hr], h.2⟩
      | [], h => exact Bool.noConfusion h
    · right
      rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        KernelFi23T2.lenK_eq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨us, by rw [Nat.eq_of_beq_eq_true h1], Nat.eq_of_beq_eq_true h2, allL_spec h3,
        incK_nodup h4⟩
  | [], h => exact Bool.noConfusion h
  | [_], h => exact Bool.noConfusion h

theorem entsW_spec : ∀ {L : List (List ℕ)}, entsW L = true → ∀ e ∈ L, wOK e = true
  | [], _, e, he => absurd he List.not_mem_nil
  | c :: L, h, e, he => by
    change bAnd(wOK c, entsW L) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact entsW_spec h.2 e he

theorem covered {i : ℕ} (hi : i < 262144)
    (hc : 2 ≤ code (Nat.shiftRight i (nat_lit 9)) (Nat.land i (nat_lit 511)))
    (hq : gL i 14566 = 14566) : ∃ e, CFSG.KD.Fi23T2.hd e = i ∧ wOK e = true := by
  have hs : i / 16384 < 16 := by omega
  have h := slAll _ hs
  unfold slF at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hcov, hents⟩ := h
  unfold covW at hcov
  have hlt : i - i / 16384 * 16384 < 16384 := by omega
  have hd' := allN_iff.1 hcov (i - i / 16384 * 16384) hlt
  have e1 : Nat.add (Nat.mul (i / 16384) (nat_lit 16384)) (i - i / 16384 * 16384) = i := by
    have : i / 16384 * 16384 + (i - i / 16384 * 16384) = i := by omega
    exact this
  have hn : ¬ Nat.blt (code (Nat.shiftRight i (nat_lit 9)) (Nat.land i (nat_lit 511)))
      (nat_lit 2) = true := fun h => by
    have h' : code (Nat.shiftRight i (nat_lit 9)) (Nat.land i (nat_lit 511)) < 2 :=
      Nat.blt_eq.mp h
    omega
  have hq' : Nat.beq (gL i qq) qq = true := by rw [qq_eq, hq]; exact Nat.beq_refl _
  rw [strictB_eq, e1, strictB_eq, bIf_eq, if_neg hn, bIf_eq, if_pos hq'] at hd'
  obtain ⟨e, he, hhd⟩ := KernelFi23T2.memH_spec hd'
  exact ⟨e, hhd, entsW_spec hents e he⟩

theorem cover_spec {x : CFSG.Sporadic.Fi23.J} (hx : InT x) (h2 : x * x = 1) (h1 : x ≠ 1) :
    (∃ m < 2048, x = pB D.B m) ∨
      ∃ g : Fin 9 → CFSG.Sporadic.Fi23.J, (∀ s, InT (g s)) ∧ Function.Injective fun s => g s * x * (g s)⁻¹ := by
  obtain ⟨i, hi, hxi⟩ := KernelFi23T2.exists_e hx.1
  have hk : Nat.shiftRight i (nat_lit 9) < 512 := by rw [KernelFi23T2.shr9]; omega
  have hj : Nat.land i (nat_lit 511) < 512 := by rw [KernelFi23T2.land511]; omega
  have hsq : ∀ b < 6, gL i (gL i b) = b := by
    intro b hb
    have h3 := congrArg (fun g => idx 31671 g b) h2
    simp only [idx_mul, idx_one] at h3
    rw [hxi, KernelFi23T2.idx_e hi (KernelFi23T2.lt_of_six hb),
      KernelFi23T2.idx_e hi (KernelFi23T2.gL_lt hi (KernelFi23T2.lt_of_six hb))] at h3
    exact h3
  have hq : gL i 14566 = 14566 := by
    have := hx.2
    rw [hxi, KernelFi23T2.idx_e hi (by norm_num)] at this
    exact this
  have hcode : 2 ≤ code (Nat.shiftRight i (nat_lit 9)) (Nat.land i (nat_lit 511)) := by
    rcases CertificateChecks.KernelFi23S.lf13_cases (CertificateChecks.KernelFi23S.lf13_all hk hj)
      with ⟨_, b, hb, hne⟩ | ⟨_, hfix⟩ | ⟨hc, _⟩ | ⟨hc, _⟩
    · exact absurd (hsq b hb) hne
    · exfalso
      apply h1
      rw [hxi]
      apply KernelFi23T2.eq_six
      intro t ht
      rw [KernelFi23T2.idx_e hi (KernelFi23T2.lt_of_six ht), idx_one]
      exact hfix t ht
    · exact hc
    · exact hc
  obtain ⟨e, hhd, hw⟩ := covered hi hcode hq
  rcases wOK_spec hw with ⟨m, -, hm⟩ | ⟨cs, -, hlen, hok, hnd⟩
  · rw [hhd] at hm
    obtain ⟨hm1, hm2⟩ := inE_spec hm
    refine Or.inl ⟨m, hm1, ?_⟩
    rw [hxi]
    apply KernelFi23T2.eq_six
    intro t ht
    rw [KernelFi23T2.idx_e hi (KernelFi23T2.lt_of_six ht),
      KernelFi23T2.idx_pB B_lt _ _ (KernelFi23T2.lt_of_six ht)]
    exact hm2 t ht
  · rw [hhd] at hnd
    have hc : ∀ s : Fin 9, okW (cs[s.val]'(by rw [hlen]; exact s.isLt)) = true :=
      fun s => hok _ (List.getElem_mem _)
    refine Or.inr ⟨fun s => wE (cs[s.val]'(by rw [hlen]; exact s.isLt)),
      fun s => inT_wE (hc s), fun s t hst => ?_⟩
    simp only at hst
    rw [hxi] at hst
    have k0 := congrArg (fun y => idx 31671 y 0) hst
    have k2 := congrArg (fun y => idx 31671 y 2) hst
    rw [idx_cj (okW_spec (hc s)).1 hi (by norm_num), idx_cj (okW_spec (hc t)).1 hi (by norm_num)]
      at k0 k2
    have hky : kyW i (cs[s.val]'(by rw [hlen]; exact s.isLt)) =
        kyW i (cs[t.val]'(by rw [hlen]; exact t.isLt)) := by
      unfold kyW
      rw [k0, k2]
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (i := s.val) (j := t.val)
      (hi := by rw [List.length_map, hlen]; exact s.isLt)
      (hj := by rw [List.length_map, hlen]; exact t.isLt)).1
      (by rw [List.getElem_map, List.getElem_map]; exact hky))

theorem clF_parts {m : ℕ} (hm : m < 3) : lenK D.P = 3 ∧ lenK D.C = 3 ∧
    CFSG.KD.Fi23T2.hd (D.C.getD m []) = D.P.getD m 0 ∧ invQ (D.P.getD m 0) = true ∧
    allN 6 (fun x => Nat.beq (gL (D.P.getD m 0) x) x) = false ∧ clW (D.C.getD m []) = true := by
  have h := clAll m hm
  unfold clF at h
  rw [strictB_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, h4, h5, h6⟩

theorem findL_spec {f : ℕ → ℕ} {l : List ℕ} (h : findL f l = true) :
    ∃ z ∈ l, ∀ p < 6, gL z p = f p := by
  unfold findL at h
  rw [strictB_eq] at h
  induction l with
  | nil => exact Bool.noConfusion h
  | cons z r ih =>
    change bIf(bAnd(Nat.beq (gL z (nat_lit 0)) (f (nat_lit 0)),
      allN (nat_lit 6) fun p => Nat.beq (gL z p) (f p)), true,
      List.rec (motive := fun _ => Bool) false
        (fun z _ ih => bIf(bAnd(Nat.beq (gL z (nat_lit 0)) (f (nat_lit 0)),
          allN (nat_lit 6) fun p => Nat.beq (gL z p) (f p)), true, ih)) r) = true at h
    rw [bIf_eq] at h
    split_ifs at h with h0
    · rw [bAnd_eq, Bool.and_eq_true] at h0
      exact ⟨z, List.mem_cons_self, fun p hp => Nat.eq_of_beq_eq_true (allN_iff.1 h0.2 p hp)⟩
    · obtain ⟨z', hz', h'⟩ := ih h
      exact ⟨z', List.mem_cons_of_mem _ hz', h'⟩

theorem clRec_spec {l : List ℕ} : ∀ {r : List ℕ}, List.rec (motive := fun _ => Bool) true
    (fun y _ ih => bAnd(Nat.blt y (nat_lit 262144),
      bAnd(allN (nat_lit 84) fun u => strictB (sw u) fun c =>
        bAnd(findL (fun p => cj c y p) l, findL (fun p => cjI c y p) l), ih))) r = true →
    ∀ y ∈ r, y < 262144 ∧ ∀ u < 84, findL (fun p => cj (sw u) y p) l = true ∧
      findL (fun p => cjI (sw u) y p) l = true
  | [], _, y, hy => absurd hy List.not_mem_nil
  | c :: r, h, y, hy => by
    change bAnd(Nat.blt c (nat_lit 262144),
      bAnd(allN (nat_lit 84) fun u => strictB (sw u) fun c' =>
        bAnd(findL (fun p => cj c' c p) l, findL (fun p => cjI c' c p) l),
      List.rec (motive := fun _ => Bool) true
        (fun y _ ih => bAnd(Nat.blt y (nat_lit 262144),
          bAnd(allN (nat_lit 84) fun u => strictB (sw u) fun c =>
            bAnd(findL (fun p => cj c y p) l, findL (fun p => cjI c y p) l), ih))) r)) = true at h
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · refine ⟨Nat.blt_eq.mp h.1, fun u hu => ?_⟩
      have h2 := allN_iff.1 h.2.1 u hu
      rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h2
      exact h2
    · exact clRec_spec h.2.2 y hy

theorem clW_spec {l : List ℕ} (h : clW l = true) : 0 < l.length ∧ l.length ≤ 8 ∧
    ∀ y ∈ l, y < 262144 ∧ ∀ u < 84, findL (fun p => cj (sw u) y p) l = true ∧
      findL (fun p => cjI (sw u) y p) l = true := by
  unfold clW at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, KernelFi23T2.lenK_eq] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.ble_eq.mp h.2.1, clRec_spec h.2.2⟩

theorem class_closed {l : List ℕ} (hall : ∀ y ∈ l, y < 262144 ∧ ∀ u < 84,
      findL (fun p => cj (sw u) y p) l = true ∧ findL (fun p => cjI (sw u) y p) l = true)
    {g : CFSG.Sporadic.Fi23.J} (hg : g ∈ Subgroup.closure {g | ∃ u < 84, wE (sw u) = g}) :
    ∀ y ∈ l, ∃ z ∈ l, g * eL y * g⁻¹ = eL z := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    intro y hy
    obtain ⟨hyb, hf⟩ := hall y hy
    obtain ⟨z, hz, hzf⟩ := findL_spec (hf u hu).1
    have hzb := (hall z hz).1
    refine ⟨z, hz, KernelFi23T2.eq_six fun p hp => ?_⟩
    rw [idx_cj (sw_spec hu).1 hyb (KernelFi23T2.lt_of_six hp),
      KernelFi23T2.idx_e hzb (KernelFi23T2.lt_of_six hp)]
    exact (hzf p hp).symm
  | inv_mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    intro y hy
    obtain ⟨hyb, hf⟩ := hall y hy
    obtain ⟨z, hz, hzf⟩ := findL_spec (hf u hu).2
    have hzb := (hall z hz).1
    refine ⟨z, hz, KernelFi23T2.eq_six fun p hp => ?_⟩
    rw [idx_cjI (sw_spec hu).1 hyb (KernelFi23T2.lt_of_six hp),
      KernelFi23T2.idx_e hzb (KernelFi23T2.lt_of_six hp)]
    exact (hzf p hp).symm
  | one => exact fun y hy => ⟨y, hy, by group⟩
  | mul x y _ _ hx hy =>
    intro w hw
    obtain ⟨z1, hz1, e1⟩ := hy w hw
    obtain ⟨z2, hz2, e2⟩ := hx z1 hz1
    exact ⟨z2, hz2, by rw [← e2, ← e1]; group⟩

theorem class_spec {m : ℕ} (hm : m < 3) :
    InT (eL (D.P.getD m 0)) ∧ eL (D.P.getD m 0) * eL (D.P.getD m 0) = 1 ∧
      eL (D.P.getD m 0) ≠ 1 ∧ (D.C.getD m []).length ≤ 8 ∧
      ∀ g ∈ Subgroup.closure {g | ∃ u < 84, wE (sw u) = g},
        ∃ z ∈ D.C.getD m [], g * eL (D.P.getD m 0) * g⁻¹ = eL z := by
  obtain ⟨-, -, hhd, hinv, hmov, hcl⟩ := clF_parts hm
  obtain ⟨hpos, hlen, hall⟩ := clW_spec hcl
  obtain ⟨hb, hbq, hbsq⟩ := invQ_spec hinv
  refine ⟨inT_eL hb hbq, eL_sq hb hbsq, fun h1 => ?_, hlen, fun g hg => ?_⟩
  · have ht : allN 6 (fun x => Nat.beq (gL (D.P.getD m 0) x) x) = true := allN_iff.2 fun x hx => by
      have h2 := congrArg (fun y => idx 31671 y x) h1
      simp only [idx_one] at h2
      rw [KernelFi23T2.idx_e hb (KernelFi23T2.lt_of_six hx)] at h2
      rw [h2]
      exact Nat.beq_refl x
    rw [ht] at hmov
    exact Bool.noConfusion hmov
  · have hmem : D.P.getD m 0 ∈ D.C.getD m [] := by
      cases hl : D.C.getD m [] with
      | nil => rw [hl] at hpos; exact absurd hpos (Nat.lt_irrefl 0)
      | cons z r =>
        have : CFSG.KD.Fi23T2.hd (D.C.getD m []) = z := by rw [hl]; rfl
        rw [← hhd, this]
        exact List.mem_cons_self
    exact class_closed hall hg _ hmem

theorem keyO_congr {c c' : ℕ} : ∀ {l : List ℕ}, (∀ y ∈ l, kyW y c = kyW y c') →
    List.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun y _ ih => Nat.lor (Nat.shiftLeft ih (nat_lit 30)) (kyW y c)) l =
    List.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun y _ ih => Nat.lor (Nat.shiftLeft ih (nat_lit 30)) (kyW y c')) l
  | [], _ => rfl
  | y :: l, h => by
    change Nat.lor (Nat.shiftLeft (List.rec (motive := fun _ => ℕ) (nat_lit 0)
        (fun y _ ih => Nat.lor (Nat.shiftLeft ih (nat_lit 30)) (kyW y c)) l) (nat_lit 30))
        (kyW y c) =
      Nat.lor (Nat.shiftLeft (List.rec (motive := fun _ => ℕ) (nat_lit 0)
        (fun y _ ih => Nat.lor (Nat.shiftLeft ih (nat_lit 30)) (kyW y c')) l) (nat_lit 30))
        (kyW y c')
    rw [keyO_congr (fun z hz => h z (List.mem_cons_of_mem _ hz)), h y List.mem_cons_self]

theorem oK_parts : D.O.length = 64 ∧ (∀ c ∈ D.O, okW c = true) ∧ (D.O.map keyO).Nodup := by
  have h := oOK
  unfold oK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, KernelFi23T2.lenK_eq] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, allL_spec h.2.1, incK_nodup h.2.2⟩

theorem orbit_spec : D.P.length = 3 ∧ ∃ g : Fin 64 → CFSG.Sporadic.Fi23.J, (∀ s, InT (g s)) ∧
    ∀ s t : Fin 64, (∀ m < 3, g s * eL (D.P.getD m 0) * (g s)⁻¹ =
      g t * eL (D.P.getD m 0) * (g t)⁻¹) → s = t := by
  have hP : D.P.length = 3 := by
    rw [← KernelFi23T2.lenK_eq]
    exact (clF_parts (m := 0) (by norm_num)).1
  obtain ⟨hlen, hok, hnd⟩ := oK_parts
  have hc : ∀ s : Fin 64, okW (D.O[s.val]'(by rw [hlen]; exact s.isLt)) = true :=
    fun s => hok _ (List.getElem_mem _)
  refine ⟨hP, fun s => wE (D.O[s.val]'(by rw [hlen]; exact s.isLt)), fun s => inT_wE (hc s),
    fun s t hst => ?_⟩
  have hky : ∀ y ∈ D.P, kyW y (D.O[s.val]'(by rw [hlen]; exact s.isLt)) =
      kyW y (D.O[t.val]'(by rw [hlen]; exact t.isLt)) := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hy
    have hm3 : m < 3 := by rw [← hP]; exact hm
    have e := List.getD_eq_getElem D.P 0 hm
    have hyb := (invQ_spec (clF_parts hm3).2.2.2.1).1
    have h := hst m hm3
    rw [← e]
    have k0 := congrArg (fun y => idx 31671 y 0) h
    have k2 := congrArg (fun y => idx 31671 y 2) h
    rw [idx_cj (okW_spec (hc s)).1 hyb (by norm_num), idx_cj (okW_spec (hc t)).1 hyb (by norm_num)]
      at k0 k2
    unfold kyW
    rw [k0, k2]
  have hk : keyO (D.O[s.val]'(by rw [hlen]; exact s.isLt)) =
      keyO (D.O[t.val]'(by rw [hlen]; exact t.isLt)) := keyO_congr hky
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (i := s.val) (j := t.val)
    (hi := by rw [List.length_map, hlen]; exact s.isLt)
    (hj := by rw [List.length_map, hlen]; exact t.isLt)).1
    (by rw [List.getElem_map, List.getElem_map]; exact hk))

end J

end CertificateChecks.KernelU62K

end
