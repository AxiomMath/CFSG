module

public import Certificates.Kernel.Fi23Five.Sound
public import Certificates.Kernel.Fi23Five.ChkDefs
public import Certificates.Kernel.Fi23R.Group
public import Certificates.Kernel.Fi23C.Group
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Fi23ThirteenInputs
import Certificates.Kernel.Fi23Five.Small
import Certificates.Kernel.Fi23Five.F0
import Certificates.Kernel.Fi23Five.F1
import Certificates.Kernel.Fi23Five.F2
import Certificates.Kernel.Fi23Five.F3
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib
public import CFSG.Sporadic.Fi23.Simple

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Five

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KD.Fi23K CFSG.KD.Fi23Five
  CFSG.KS.Raw.Orb CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M
  CertificateChecks.KernelFi23R CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

local notation "T1" => starWordTab orbLit (dTable orbLit) (genTables orbLit (-2)) path

local notation "pe" => wp eW
local notation "pf" => wp fW

theorem beq_eq_nbeq (a b : Nat) : (a == b) = Nat.beq a b := by
  cases e : Nat.beq a b
  · exact beq_false_of_ne (Nat.ne_of_beq_eq_false e)
  · exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true e)

theorem findSome_mem_congr {β : Type} {f g : Nat → Option β} :
    ∀ l : List Nat, (∀ x ∈ l, f x = g x) → l.findSome? f = l.findSome? g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.findSome?_cons, List.findSome?_cons, h a List.mem_cons_self,
      findSome_mem_congr l fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem pathSearch_congr {c c' : Nat → Nat → Bool} {F : List Nat}
    (h : ∀ i ∈ F, ∀ j ∈ F, c i j = c' i j) : pathSearch c F = pathSearch c' F := by
  unfold pathSearch
  congr 1
  apply findSome_mem_congr
  intro i₁ h₁
  apply findSome_mem_congr
  intro i₂ h₂
  rw [h i₁ h₁ i₂ h₂]
  congr 1
  apply findSome_mem_congr
  intro i₃ h₃
  rw [h i₂ h₂ i₃ h₃, h i₁ h₁ i₃ h₃]
  congr 1
  apply findSome_mem_congr
  intro i₄ h₄
  rw [h i₃ h₃ i₄ h₄, h i₁ h₁ i₄ h₄, h i₂ h₂ i₄ h₄]

theorem graphOK_mono {c c' : Nat → Nat → Bool} {L : List Nat}
    (h : ∀ i ∈ L, ∀ j ∈ L, c i j = c' i j) (hg : graphOK c L = true) : graphOK c' L = true := by
  unfold graphOK at hg ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true] at hg ⊢
  obtain ⟨⟨h0, h1⟩, h2⟩ := hg
  refine ⟨⟨h0, fun i hi => ?_⟩, fun i hi j hj => ?_⟩
  · obtain ⟨j, hj, hc⟩ := h1 i hi
    rw [h i hi j hj] at hc
    exact ⟨j, hj, hc⟩
  · rcases h2 i hi j hj with hc | ⟨k, hk, hc⟩
    · rw [h i hi j hj] at hc
      exact Or.inl hc
    · rw [h k hk i hi, h k hk j hj] at hc
      exact Or.inr ⟨k, hk, hc⟩

theorem eqTab_self (A : Table) : eqTab A A = true := by
  unfold eqTab
  rw [List.all_eq_true]
  intro i _
  exact beq_self_eq_true _

theorem eqTab_false {A B : Table} {i : Nat} (hi : i < 31671) (h : ap A i ≠ ap B i) :
    eqTab A B = false := by
  unfold eqTab
  cases e : (List.range 31671).all fun i => ap A i == ap B i
  · rfl
  · rw [List.all_eq_true] at e
    exact absurd (beq_iff_eq.1 (e i (List.mem_range.2 hi))) h

theorem pow_fix (q : Pt) (x : Fin 31671) (h : q x = x) : ∀ j : Nat, (q ^ j) x = x
  | 0 => rfl
  | j + 1 => by rw [pow_succ, Equiv.Perm.mul_apply, h, pow_fix q x h j]

theorem pow_mod5 {r : Pt} (h5 : r ^ 5 = 1) (n : Nat) : r ^ n = r ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, h5, one_pow, one_mul]

theorem fix_pow_iff {r : Pt} (h5 : r ^ 5 = 1) {k : Nat} (hk0 : 0 < k) (hk5 : k < 5)
    (x : Fin 31671) : (r ^ k) x = x ↔ r x = x := by
  constructor
  · intro h
    have hm : ∃ m, (k * m) % 5 = 1 := by
      interval_cases k
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨4, rfl⟩
    obtain ⟨m, hm⟩ := hm
    have e : (r ^ k) ^ m = r := by rw [← pow_mul, pow_mod5 h5, hm, pow_one]
    rw [← e]
    exact pow_fix _ x h m
  · intro h
    exact pow_fix r x h k

section


theorem tb_e {x : Nat} (hx : x < 31671) : tb H 0 x = wa G eW x := by
  rcases Nat.lt_or_ge x 16384 with h | h
  · exact regSl_spec eReg0_ok x (Nat.zero_le x) (by omega)
  · exact regSl_spec eReg1_ok x (by omega) (by omega)

theorem tb_f {x : Nat} (hx : x < 31671) : tb H 1 x = wa G fW x := by
  have hk : x / 2048 < 16 := by omega
  have h1 : 2048 * (x / 2048) ≤ x := Nat.mul_div_le x 2048
  have h2 : x < 2048 * (x / 2048) + 2048 := by omega
  generalize x / 2048 = k at hk h1 h2
  interval_cases k
  · exact regSl_spec fReg0_ok x (Nat.zero_le x) (by omega)
  · exact regSl_spec fReg1_ok x (by omega) (by omega)
  · exact regSl_spec fReg2_ok x (by omega) (by omega)
  · exact regSl_spec fReg3_ok x (by omega) (by omega)
  · exact regSl_spec fReg4_ok x (by omega) (by omega)
  · exact regSl_spec fReg5_ok x (by omega) (by omega)
  · exact regSl_spec fReg6_ok x (by omega) (by omega)
  · exact regSl_spec fReg7_ok x (by omega) (by omega)
  · exact regSl_spec fReg8_ok x (by omega) (by omega)
  · exact regSl_spec fReg9_ok x (by omega) (by omega)
  · exact regSl_spec fReg10_ok x (by omega) (by omega)
  · exact regSl_spec fReg11_ok x (by omega) (by omega)
  · exact regSl_spec fReg12_ok x (by omega) (by omega)
  · exact regSl_spec fReg13_ok x (by omega) (by omega)
  · exact regSl_spec fReg14_ok x (by omega) (by omega)
  · exact regSl_spec fReg15_ok x (by omega) (by omega)

theorem okE : ∀ c ∈ eW, okL c := by decide

theorem okF : ∀ c ∈ fW, okL c := by decide

noncomputable def hp : List Nat → Pt
  | [] => 1
  | c :: L => (if c = 0 then pe else pf) * hp L

theorem wv_hp : ∀ L : List Nat, (∀ c ∈ L, c = 0 ∨ c = 1) → ActsAs (hp L) (wv H L)
  | [], _ => fun _ _ => rfl
  | c :: L, hL => by
    intro x hx
    have ih := wv_hp L (fun d hd => hL d (List.mem_cons_of_mem c hd)) x hx
    rw [hp, Equiv.Perm.mul_apply, wv_cons, ← ih]
    rcases hL c List.mem_cons_self with rfl | rfl
    · rw [if_pos rfl, tb_e (Fin.isLt _)]
      exact wp_acts eW okE _ _
    · rw [if_neg one_ne_zero, tb_f (Fin.isLt _)]
      exact wp_acts fW okF _ _

theorem hp_replicate : ∀ n : Nat, hp (List.replicate n 1) = pf ^ n
  | 0 => by rw [List.replicate_zero, hp, pow_zero]
  | n + 1 => by rw [List.replicate_succ, hp, if_neg one_ne_zero, hp_replicate n, pow_succ']

theorem small_parts : eqB G (powW 5 eW) [] = true ∧ eqB G (powW 5 fW) [] = true ∧
    eqB G (eW ++ fW) (fW ++ eW) = true ∧ eqB G eW [] = false ∧
    ∀ k < 5, eqB G fW (powW k eW) = false := by
  have h := smallK_ok
  unfold smallK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun k hk => h5 k ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem eqB_ne {u v : List Nat} (h : eqB G u v = false) : ∃ b < 6, wa G u b ≠ wa G v b := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  have ht : eqB G u v = true := allN_iff.2 fun b hb => by simp only [hc b hb, Nat.beq_refl]
  rw [h] at ht
  exact Bool.false_ne_true ht

theorem nil_ok : ∀ c ∈ ([] : List Nat), okL c := fun _ h => absurd h List.not_mem_nil

theorem e5 : wp (powW 5 eW) = wp [] := wp_eq_of_eqB small_parts.1 (ok_powW okE 5) nil_ok

theorem f5 : wp (powW 5 fW) = wp [] := wp_eq_of_eqB small_parts.2.1 (ok_powW okF 5) nil_ok

theorem he5 : pe ^ 5 = 1 := by
  have h := e5
  rwa [wp_powW, wp_nil] at h

theorem hf5 : pf ^ 5 = 1 := by
  have h := f5
  rwa [wp_powW, wp_nil] at h

theorem efe : wp (eW ++ fW) = wp (fW ++ eW) :=
  wp_eq_of_eqB small_parts.2.2.1 (ok_append okE okF) (ok_append okF okE)

theorem hcomm : Commute pe pf := by
  have h := efe
  rw [wp_append, wp_append] at h
  exact h.symm

theorem dTable_eq : dTable orbLit = dTab orbLit := by
  have h : RW (dTable orbLit) [43] := rw_of_acts (powT_size (dWordTable orbLit) 7) (by decide)
    fun i hi => by rw [KernelFi23C.dTable_ap hi, wa_cons, wa_nil, lf_eq, if_pos (by norm_num)]
  exact beq_iff_eq.1 (RW.beq h rw_dTab rfl)

theorem eLetters_ok : ∀ z ∈ eLetters, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by decide

theorem rw_e : RW (eTab orbLit) eW := (rw_wordT eLetters eLetters_ok).word (by decide)

theorem rw_f : RW T1 fW := by
  rw [dTable_eq]
  unfold starWordTab path
  simp only [List.foldr_cons, List.foldr_nil]
  exact (rw_compT (rw_treeActTab (k := 777) (by norm_num))
    (rw_compT (rw_treeActTab (k := 11568) (by norm_num))
      (rw_compT (rw_treeActTab (k := 8258) (by norm_num))
        (rw_compT (rw_treeActTab (k := 17218) (by norm_num)) rw_idT)))).word (by decide)

theorem commB_eq {i j : Nat} (hi : i < 31671) (hj : j < 31671) :
    commB orbLit (dTable orbLit) (genTables orbLit (-2)) i j = cmK G i j := by
  unfold commB cmK
  rw [tAf_treeAct (fun m hm => KernelFi23C.dTable_ap hm) (fun m hm => KernelFi23C.bi_ap hm) 200 i hi
    (dep_pt hi).1 j hj]
  exact beq_eq_nbeq _ _

theorem fixList_of {T : Table} {w L : List Nat} (hT : ∀ i < 31671, ap T i = wv H w i)
    (hk : fixK H w L = true) : fixList T = L := by
  rw [← fixK_spec hk]
  unfold fixList
  apply List.filter_congr
  intro i hi
  rw [hT i (List.mem_range.1 hi), beq_eq_nbeq]

theorem lt_lE {i : Nat} (h : i ∈ lE) : i < 31671 := by
  rw [← fixK_spec fixE_ok] at h
  exact List.mem_range.1 (List.mem_filter.1 h).1

theorem path_eq : fivePathOf orbLit = path := by
  have hfix : fixList (eTab orbLit) = lE := fixList_of (fun i hi => by
    rw [rw_e.ap hi, wv_cons, wv_nil, tb_e hi]) fixE_ok
  unfold fivePathOf
  rw [hfix, pathSearch_congr (c' := cmK G) fun i hi j hj => commB_eq (lt_lE hi) (lt_lE hj)]
  exact beq_iff_eq.1 pathOK_ok

def repW (a b : Nat) : List Nat := if a = 0 then [1] else 0 :: List.replicate ((b * a ^ 3) % 5) 1

def repL (a b : Nat) : List Nat :=
  if a = 0 then lF else [lE, lEF, lEF2, lEF3, lEF4].getD ((b * a ^ 3) % 5) []

theorem repW_ok (a b : Nat) : ∀ c ∈ repW a b, c = 0 ∨ c = 1 := by
  unfold repW
  split_ifs
  · intro c hc
    rw [List.mem_singleton] at hc
    exact Or.inr hc
  · intro c hc
    rcases List.mem_cons.1 hc with h | h
    · exact Or.inl h
    · exact Or.inr (List.eq_of_mem_replicate h)

theorem rep_ok (a b : Nat) : fixK H (repW a b) (repL a b) = true := by
  unfold repW repL
  split_ifs
  · exact fixF_ok
  · have hc : (b * a ^ 3) % 5 < 5 := Nat.mod_lt _ (by norm_num)
    generalize (b * a ^ 3) % 5 = c at hc ⊢
    interval_cases c
    · exact fixE_ok
    · exact fixEF_ok
    · exact fixEF2_ok
    · exact fixEF3_ok
    · exact fixEF4_ok

theorem gr_rep (a b : Nat) : graphOK (cmK G) (repL a b) = true := by
  unfold repL
  split_ifs
  · exact grF_ok
  · have hc : (b * a ^ 3) % 5 < 5 := Nat.mod_lt _ (by norm_num)
    generalize (b * a ^ 3) % 5 = c at hc ⊢
    interval_cases c
    · exact grE_ok
    · exact grEF_ok
    · exact grEF2_ok
    · exact grEF3_ok
    · exact grEF4_ok

theorem len_repL (a b : Nat) : (repL a b).length = 21 := by
  unfold repL
  split_ifs
  · rfl
  · have hc : (b * a ^ 3) % 5 < 5 := Nat.mod_lt _ (by norm_num)
    generalize (b * a ^ 3) % 5 = c at hc ⊢
    interval_cases c <;> rfl

theorem lt_repL {a b i : Nat} (h : i ∈ repL a b) : i < 31671 := by
  rw [← fixK_spec (rep_ok a b)] at h
  exact List.mem_range.1 (List.mem_filter.1 h).1

theorem key_mod : ∀ a < 5, ∀ b < 5, a ≠ 0 → (b * a ^ 3 % 5 * a) % 5 = b := by decide

theorem rep_pow (a b : Nat) (ha : a < 5) (hb : b < 5) (hab : a + b ≠ 0) :
    hp (repW a b) ^ 5 = 1 ∧ ∃ k, 0 < k ∧ k < 5 ∧ pe ^ a * pf ^ b = hp (repW a b) ^ k := by
  unfold repW
  split_ifs with h0
  · subst h0
    have e : hp [1] = pf := by rw [hp, hp, if_neg one_ne_zero, mul_one]
    rw [e]
    exact ⟨hf5, b, by omega, hb, by rw [pow_zero, one_mul]⟩
  · have e : hp (0 :: List.replicate ((b * a ^ 3) % 5) 1) = pe * pf ^ ((b * a ^ 3) % 5) := by
      rw [hp, if_pos rfl, hp_replicate]
    rw [e]
    have hc : Commute pe (pf ^ ((b * a ^ 3) % 5)) := hcomm.pow_right _
    refine ⟨?_, a, by omega, ha, ?_⟩
    · rw [hc.mul_pow, he5, one_mul, pow_right_comm, hf5, one_pow]
    · rw [hc.mul_pow, ← pow_mul, pow_mod5 hf5 ((b * a ^ 3) % 5 * a), key_mod a ha b hb h0]

theorem rw_five (a b : Nat) : RW (fiveTab (eTab orbLit) T1 a b) (powW b fW ++ powW a eW) :=
  rw_compT (rw_powT rw_e a) (rw_powT rw_f b)

theorem ap_five (a b : Nat) {i : Nat} (hi : i < 31671) :
    ap (fiveTab (eTab orbLit) T1 a b) i = ((pe ^ a * pf ^ b) ⟨i, hi⟩).val := by
  rw [(rw_five a b).ap hi, ← wp_acts _ (rw_five a b).2.1 i hi, wp_append, wp_powW, wp_powW]

theorem fix_main {a b : Nat} (ha : a < 5) (hb : b < 5) (hab : a + b ≠ 0) :
    fixList (fiveTab (eTab orbLit) T1 a b) = repL a b := by
  rw [← fixK_spec (rep_ok a b)]
  unfold fixList
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  obtain ⟨h5, k, hk0, hk5, hk⟩ := rep_pow a b ha hb hab
  have hf := fix_pow_iff h5 hk0 hk5 ⟨i, hi'⟩
  rw [← hk, Fin.ext_iff, Fin.ext_iff] at hf
  rw [ap_five a b hi', ← wv_hp _ (repW_ok a b) i hi', beq_eq_nbeq]
  exact Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, Nat.beq_eq]; exact hf)

theorem core_ok :
    fi23FiveCore orbLit (dTable orbLit) (genTables orbLit (-2)) (eTab orbLit) T1 = true := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := small_parts
  have q1 : powT 31671 5 (eTab orbLit) = idT 31671 :=
    beq_iff_eq.1 (RW.beq (rw_powT rw_e 5) rw_idT e5)
  have q2 : powT 31671 5 T1 = idT 31671 := beq_iff_eq.1 (RW.beq (rw_powT rw_f 5) rw_idT f5)
  have q3 : compT 31671 (eTab orbLit) T1 = compT 31671 T1 (eTab orbLit) :=
    beq_iff_eq.1 (RW.beq (rw_compT rw_e rw_f) (rw_compT rw_f rw_e) efe.symm)
  unfold fi23FiveCore
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨by rw [q1]; exact eqTab_self _, ?_⟩, by rw [q2]; exact eqTab_self _⟩,
    by rw [q3]; exact eqTab_self _⟩, fun k hk => ?_⟩, fun a ha b hb => ?_⟩
  · obtain ⟨x, hx, hne⟩ := eqB_ne s4
    exact eqTab_false (i := x) (by omega)
      (by rw [rw_e.ap (by omega), rw_idT.ap (by omega)]; exact hne)
  · obtain ⟨x, hx, hne⟩ := eqB_ne (s5 k hk)
    exact eqTab_false (i := x) (by omega)
      (by rw [rw_f.ap (by omega), (rw_powT rw_e k).ap (by omega)]; exact hne)
  · by_cases hab : a + b = 0
    · exact Or.inl hab
    · right
      rw [fix_main ha hb hab]
      exact graphOK_mono (fun i hi j hj => (commB_eq (lt_repL hi) (lt_repL hj)).symm) (gr_rep a b)

theorem five_ok : fi23FiveOK orbLit = true := by
  unfold fi23FiveOK
  dsimp only
  rw [path_eq, Bool.and_eq_true]
  exact ⟨by decide, core_ok⟩

theorem thirteen_ok :
    CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23ThirteenNative.fi23ThirteenOK orbLit = true := by
  unfold CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23ThirteenNative.fi23ThirteenOK
  dsimp only
  rw [path_eq, List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  by_cases hab : a + b = 0
  · simp [hab]
  · rw [fix_main (List.mem_range.1 ha) (List.mem_range.1 hb) hab, len_repL]
    simp

end

end CertificateChecks.KernelFi23Five

end
