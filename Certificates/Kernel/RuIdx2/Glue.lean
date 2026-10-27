module

import Certificates.Kernel.RuIdx2.E0a
import Certificates.Kernel.RuIdx2.E0b
import Certificates.Kernel.RuIdx2.E1a
import Certificates.Kernel.RuIdx2.E1b
import Certificates.Kernel.RuIdx2.E2a
import Certificates.Kernel.RuIdx2.E2b
import Certificates.Kernel.RuIdx2.E3a
import Certificates.Kernel.RuIdx2.E3b
import Certificates.Kernel.RuIdx2.E4a
import Certificates.Kernel.RuIdx2.E4b
import Certificates.Kernel.RuIdx2.E5a
import Certificates.Kernel.RuIdx2.E5b
import Certificates.Kernel.RuIdx2.E6a
import Certificates.Kernel.RuIdx2.E6b
import Certificates.Kernel.RuIdx2.M0
import Certificates.Kernel.RuIdx2.M1
import Certificates.Kernel.RuIdx2.M2
import Certificates.Kernel.RuIdx2.M3
import Certificates.Kernel.RuIdx2.M4
import Certificates.Kernel.RuIdx2.M5
import Certificates.Kernel.RuIdx2.M6
import Certificates.Kernel.RuIdx2.W
public import Certificates.Kernel.RuIdx2.Lab

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2.Glue

open CFSG.KD.RuIdx2 CFSG.KD.RuIdx2.Sem CFSG.KC.RuIdx2 CFSG.KC.Enum CFSG.KC.Kc3K CFSG.KS
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.K1262Two.RuP
open CFSG.KD.RuIdx2.Lab (Rv idx2_v X_mem lab_X lt_IL lt_sq RW_lt)

theorem allIdx_spec {f : Nat → Nat → Bool} : ∀ {lo : Nat} {L : List Nat}, allIdx f lo L = true →
    ∀ i < L.length, f (lo + i) (L.getD i 0) = true
  | _, [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | lo, it :: L, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false (strictB (Nat.succ lo) fun j => allIdx f j L)
      (f lo it) = true at h
    simp only [PK.bAnd_eq, PK.strictB_eq, Bool.and_eq_true] at h
    rcases i with _ | i
    · exact h.1
    · have e : lo + (i + 1) = Nat.succ lo + i := by omega
      rw [e, List.getD_cons_succ]
      exact allIdx_spec h.2 i (by simpa using hi)

theorem memN_false {x : Nat} : ∀ {L : List Nat}, x ∉ L → memN x L = false
  | [], _ => rfl
  | y :: L, h => by
    have hxy : x ≠ y := fun e => h (e ▸ List.mem_cons_self)
    have ih := memN_false (L := L) fun hm => h (List.mem_cons_of_mem _ hm)
    change Bool.rec (motive := fun _ => Bool) (memN x L) true (Nat.beq x y) = false
    rw [PK.bIf_eq, if_neg (by simpa using hxy), ih]

theorem fam_split {f : Nat → Bool} {k m : Nat} (hA : ∀ i < k, f (Nat.add 0 i) = true)
    (hB : ∀ i < m, f (Nat.add k i) = true) : ∀ c < k + m, f c = true := by
  intro c hc
  by_cases h : c < k
  · simpa using hA c h
  · have e : Nat.add k (c - k) = c := by
      change k + (c - k) = c
      omega
    rw [← e]
    exact hB (c - k) (by omega)

theorem shl6 (x : Nat) : Nat.shiftLeft x 6 = x * 64 := by
  change x <<< 6 = _
  rw [Nat.shiftLeft_eq]

theorem edge_of_famE {u n : Nat} (hn1 : 1 ≤ n) (hn : n < nR u) (hc : famE u ((n - 1) / 64) = true) :
    ∃ it, edgeK LC IL (RG u) (RW u) Bs (nr u) n it = true := by
  unfold famE at hc
  simp only [PK.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hc
  obtain ⟨hlen, hall⟩ := hc
  have hlen' : (CFSG.KD.RuIdx2.E u ((n - 1) / 64)).length =
      min 64 (nR u - 1 - (n - 1) / 64 * 64) := by
    rw [hlen, shl6]
    rfl
  have h := allIdx_spec hall ((n - 1) % 64) (by rw [hlen']; omega)
  have e : Nat.add 1 (Nat.shiftLeft ((n - 1) / 64) 6) + (n - 1) % 64 = n := by
    rw [shl6]
    change 1 + (n - 1) / 64 * 64 + (n - 1) % 64 = n
    omega
  rw [e] at h
  exact ⟨_, h⟩

theorem match_of_famM {u p : Nat} (hp : p < 1678) (hex : p ∉ ex u) (hc : famM u (p / 64) = true) :
    ∃ it, matchK LC (RW u) XW psi Ru4120.TF Ru4120.eu Ru4120.ev Bs (nR u) (vm u) (tau u) p it =
      true := by
  unfold famM at hc
  simp only [PK.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hc
  obtain ⟨hlen, hall⟩ := hc
  have hlen' : (CFSG.KD.RuIdx2.M u (p / 64)).length = min 64 (1678 - p / 64 * 64) := by
    rw [hlen, shl6]
    rfl
  have h := allIdx_spec hall (p % 64) (by rw [hlen']; omega)
  have e : Nat.shiftLeft (p / 64) 6 + p % 64 = p := by
    rw [shl6]
    omega
  rw [e, PK.bIf_eq, memN_false hex] at h
  exact ⟨_, h⟩

theorem famE_ok {u : Nat} (hu : u < 7) {n : Nat} (hn1 : 1 ≤ n) (hn : n < nR u) :
    famE u ((n - 1) / 64) = true := by
  interval_cases u
  · exact fam_split (f := famE 0) (k := 14) (m := 13) (fun i hi => E0a.all i hi)
      (fun i hi => E0b.all i hi) _ (by change n < 1684 at hn; omega)
  · exact fam_split (f := famE 1) (k := 13) (m := 13) (fun i hi => E1a.all i hi)
      (fun i hi => E1b.all i hi) _ (by change n < 1612 at hn; omega)
  · exact fam_split (f := famE 2) (k := 13) (m := 13) (fun i hi => E2a.all i hi)
      (fun i hi => E2b.all i hi) _ (by change n < 1633 at hn; omega)
  · exact fam_split (f := famE 3) (k := 13) (m := 12) (fun i hi => E3a.all i hi)
      (fun i hi => E3b.all i hi) _ (by change n < 1555 at hn; omega)
  · exact fam_split (f := famE 4) (k := 12) (m := 12) (fun i hi => E4a.all i hi)
      (fun i hi => E4b.all i hi) _ (by change n < 1535 at hn; omega)
  · exact fam_split (f := famE 5) (k := 12) (m := 12) (fun i hi => E5a.all i hi)
      (fun i hi => E5b.all i hi) _ (by change n < 1499 at hn; omega)
  · exact fam_split (f := famE 6) (k := 12) (m := 11) (fun i hi => E6a.all i hi)
      (fun i hi => E6b.all i hi) _ (by change n < 1471 at hn; omega)

theorem famM_ok {u : Nat} (hu : u < 7) {c : Nat} (hc : c < 27) : famM u c = true := by
  interval_cases u
  exacts [M0.all c hc, M1.all c hc, M2.all c hc, M3.all c hc, M4.all c hc, M5.all c hc,
    M6.all c hc]

theorem RG_lt : ∀ u < 7, ∀ l < nr u, ∀ c ∈ unW (RG u l), c < 10 := by decide

theorem bs_lt : ∀ p ∈ Bs, p < 4060 := by decide

section Group

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 4060)] {a b : Γ}

structure RF (a b : Γ) (u : Nat) : Prop where
  le : Rv a b u ≤ Ru4120.H.RX a b
  card : Nat.card (Ru4120.H.RX a b) = 2 * Nat.card (Rv a b u)
  mem : ∀ k < 16384, Ru4120.H.X a b k ∈ Ru4120.H.RX a b ∧
    (Ru4120.H.X a b k ∈ Rv a b u ↔ par (vm u) (psi k) = 0)

theorem par_lt (vm x : Nat) : par vm x < 2 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem cast_eq_zero {n : Nat} (hn : n < 2) : ((n : Nat) : ZMod 2) = 0 ↔ n = 0 := by
  interval_cases n <;> decide

theorem rf [Finite Γ] (h : Ru4120.H.Ctx a b) (hc : Nat.card (Ru4120.H.RX a b) = 2 ^ 14) {u : Nat}
    (hu : u < 7) : RF a b u := by
  obtain ⟨hle, hiff, hcard, -⟩ := idx2_v h hc hu
  refine ⟨hle, hcard, fun k hk => ⟨X_mem h hc hk, ?_⟩⟩
  rw [hiff _ (X_mem h hc hk), lab_X h hc _ hk, cast_eq_zero (par_lt _ _)]

theorem act_wE (h : Ru4120.H.Ctx a b) (W : Nat) {p : Nat} (hp : p < 4060) :
    act 4060 (wE a b W) p = wp LC W p :=
  (wp_eq h W hp).symm

theorem hinv (h : Ru4120.H.Ctx a b) : ∀ c < 10, lt a b (IL c) = (lt a b c)⁻¹ :=
  fun _ hc => lt_IL h hc

theorem tau_sq (h : Ru4120.H.Ctx a b) : lt a b (tau 2) * lt a b (tau 2) = 1 :=
  lt_sq h (c := 4) (by norm_num) (by norm_num)

theorem act_tp (h : Ru4120.H.Ctx a b) (o t : Nat) {q : Nat} (hq : q < 4060) :
    act 4060 (if o = 1 then lt a b t else 1) q = tp LC o t q := by
  unfold tp
  simp only [PK.nIf_eq, Nat.beq_eq]
  split_ifs
  · exact act_let h t hq
  · exact act_one hq

variable [Finite Γ]

theorem edge_mem (h : Ru4120.H.Ctx a b) {u n it : Nat} (hu : u < 7)
    (hX : ∀ c ∈ unW (RW u n), c < 10) (he : edgeK LC IL (RG u) (RW u) Bs (nr u) n it = true) :
    Nat.land it 4095 < n ∧
      wE a b (RW u (Nat.land it 4095)) ∈ Rv a b u ⊔ Subgroup.zpowers (wE a b (RW u n)) := by
  unfold edgeK at he
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true,
    Nat.beq_eq] at he
  obtain ⟨hd, hb⟩ := he
  refine ⟨hd, ?_⟩
  have e : wE a b (RW u (Nat.land it 4095)) =
      epE a b (RG u) (nr u) (RW u n) (Nat.shiftRight it 12) :=
    eq_of_Bs h fun p hp => by
      have hp' := bs_lt p hp
      rw [← wp_eq h _ hp', ← ep_eq h (hinv h) _ _ _ (RG_lt u hu) hX _ hp']
      exact hb p hp
  rw [e]
  exact epE_mem _ _ _ _ _ fun l hl => Lab.gen_mem hl

theorem good_root (h : Ru4120.H.Ctx a b) {u : Nat} (hu : u < 7) (hF : RF a b u)
    (hX : ∀ c ∈ unW (RW u 0), c < 10) :
    Good (Rv a b u) (Ru4120.H.RX a b) (wE a b (RW u 0)) := by
  have hw := CFSG.KD.RuIdx2.W.all u hu
  unfold famW witK at hw
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    List.all_eq_true] at hw
  obtain ⟨hkt, hpr, hpt, hb⟩ := hw
  have hkr : Nat.land (WK u) 16383 < 16384 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hg : wE a b (WX u) ∈ Rv a b u ⊔ Subgroup.zpowers (wE a b (RW u 0)) := by
    have e : wE a b (WX u) = epE a b (RG u) (nr u) (RW u 0) (WE u) :=
      eq_of_Bs h fun p hp => by
        have hp' := bs_lt p hp
        rw [← wp_eq h _ hp', ← ep_eq h (hinv h) _ _ _ (RG_lt u hu) hX _ hp']
        exact (hb p hp).1
    rw [e]
    exact epE_mem _ _ _ _ _ fun l hl => Lab.gen_mem hl
  have hc : wE a b (WX u) * Ru4120.H.X a b (Nat.land (WK u) 16383) =
      Ru4120.H.X a b (Nat.shiftRight (WK u) 14) * wE a b (WX u) :=
    eq_of_Bs h fun p hp => by
      have hp' := bs_lt p hp
      have h1 : exK 12 4095 Ru4120.TF (Ru4120.eu (Nat.land (WK u) 16383))
          (Ru4120.ev (Nat.land (WK u) 16383)) p < 4060 := by
        rw [← Ru4120.H.act_X h hkr hp']
        exact act_lt _ hp'
      have h2 : wp LC (WX u) p < 4060 := by
        rw [wp_eq h _ hp']
        exact act_lt _ hp'
      rw [act_mul _ _ hp', act_mul _ _ hp', Ru4120.H.act_X h hkr hp', act_wE h _ h1,
        act_wE h _ hp', Ru4120.H.act_X h hkt h2]
      exact (hb p hp).2
  have hm := hF.mem _ hkt
  refine ⟨_, hm.1, fun hR => absurd (hm.2.1 hR) (by rw [hpt]; decide), ?_⟩
  have e : Ru4120.H.X a b (Nat.shiftRight (WK u) 14) =
      wE a b (WX u) * Ru4120.H.X a b (Nat.land (WK u) 16383) * (wE a b (WX u))⁻¹ := by
    rw [hc, mul_inv_cancel_right]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg
    (Subgroup.mem_sup_left ((hF.mem _ hkr).2.2 hpr))) (Subgroup.inv_mem _ hg)

theorem good_reps (h : Ru4120.H.Ctx a b) {u : Nat} (hu : u < 7) (hF : RF a b u)
    (hRW : ∀ i < nR u, ∀ c ∈ unW (RW u i), c < 10) :
    ∀ n < nR u, Good (Rv a b u) (Ru4120.H.RX a b) (wE a b (RW u n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact good_root h hu hF (hRW 0 hn)
    · obtain ⟨it, he⟩ := edge_of_famE hpos hn (famE_ok hu hpos hn)
      obtain ⟨hd, hm⟩ := edge_mem h hu (hRW n hn) he
      exact good_of_mem hm (ih _ hd (by omega))

theorem match_good (h : Ru4120.H.Ctx a b) {u p it : Nat} (hF : RF a b u)
    (hgood : ∀ i < nR u, Good (Rv a b u) (Ru4120.H.RX a b) (wE a b (RW u i)))
    (hm : matchK LC (RW u) XW psi Ru4120.TF Ru4120.eu Ru4120.ev Bs (nR u) (vm u) (tau u) p it =
      true) :
    Good (Rv a b u) (Ru4120.H.RX a b)
      ((if Nat.land p 1 = 1 then lt a b (tau u) else 1) * wE a b (XW (Nat.shiftRight p 1))) := by
  unfold matchK at hm
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    List.all_eq_true] at hm
  obtain ⟨hi, hk2, hp1, hp2, hb⟩ := hm
  have hk1 : Nat.land (Nat.shiftRight it 12) 16383 < 16384 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have e : wE a b (RW u (Nat.land it 4095)) =
      Ru4120.H.X a b (Nat.land (Nat.shiftRight it 12) 16383) *
        ((if Nat.land p 1 = 1 then lt a b (tau u) else 1) * wE a b (XW (Nat.shiftRight p 1))) *
        Ru4120.H.X a b (Nat.shiftRight it 26) :=
    eq_of_Bs h fun q hq => by
      have hq' := bs_lt q hq
      have hq2 := act_lt (Ru4120.H.X a b (Nat.shiftRight it 26)) hq'
      have hq3 := act_lt (wE a b (XW (Nat.shiftRight p 1))) hq2
      have hq4 := act_lt (if Nat.land p 1 = 1 then lt a b (tau u) else 1) hq3
      rw [act_wE h _ hq', act_mul _ _ hq', act_mul _ _ hq2, act_mul _ _ hq2,
        Ru4120.H.act_X h hk1 hq4, act_tp h _ _ hq3, act_wE h _ hq2, Ru4120.H.act_X h hk2 hq']
      exact hb q hq
  refine good_of_mem ?_ (hgood _ hi)
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left ((hF.mem _ hk1).2.2 hp1)) (mem_sup_zpowers _ _))
    (Subgroup.mem_sup_left ((hF.mem _ hk2).2.2 hp2))

theorem good_pos (h : Ru4120.H.Ctx a b) {u : Nat} (hu : u < 7) (hF : RF a b u)
    (hRW : ∀ i < nR u, ∀ c ∈ unW (RW u i), c < 10) {p : Nat} (hp : p < 1678) (hex : p ∉ ex u) :
    Good (Rv a b u) (Ru4120.H.RX a b)
      ((if Nat.land p 1 = 1 then lt a b (tau u) else 1) * wE a b (XW (Nat.shiftRight p 1))) := by
  obtain ⟨it, hm⟩ := match_of_famM hp hex (famM_ok hu (by omega))
  exact match_good h hF (good_reps h hu hF hRW) hm

theorem good_x (h : Ru4120.H.Ctx a b) (hc : Nat.card (Ru4120.H.RX a b) = 2 ^ 14) {u : Nat}
    (hu : u < 7) {j : Nat} (hj : j < 839) (hex : 2 * j ∉ ex u) :
    Good (Rv a b u) (Ru4120.H.RX a b) (wE a b (XW j)) := by
  have g := good_pos h hu (rf h hc hu) (fun _ hi => RW_lt hu hi) (p := 2 * j) (by omega) hex
  have e1 : Nat.land (2 * j) 1 = 0 := by
    change (2 * j) &&& 1 = 0
    rw [Nat.and_one_is_mod]
    omega
  have e2 : Nat.shiftRight (2 * j) 1 = j := by
    change (2 * j) >>> 1 = j
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [e1, e2, if_neg (by decide), one_mul] at g
  exact g

theorem good_tx (h : Ru4120.H.Ctx a b) (hc : Nat.card (Ru4120.H.RX a b) = 2 ^ 14) {u : Nat}
    (hu : u < 7) {j : Nat} (hj : j < 839) (hex : 2 * j + 1 ∉ ex u) :
    Good (Rv a b u) (Ru4120.H.RX a b) (lt a b (tau u) * wE a b (XW j)) := by
  have g := good_pos h hu (rf h hc hu) (fun _ hi => RW_lt hu hi) (p := 2 * j + 1) (by omega)
    hex
  have e1 : Nat.land (2 * j + 1) 1 = 1 := by
    change (2 * j + 1) &&& 1 = 1
    rw [Nat.and_one_is_mod]
    omega
  have e2 : Nat.shiftRight (2 * j + 1) 1 = j := by
    change ((2 * j + 1) >>> 1) = j
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [e1, e2, if_pos rfl] at g
  exact g

end Group

end CFSG.KD.RuIdx2.Glue

end
