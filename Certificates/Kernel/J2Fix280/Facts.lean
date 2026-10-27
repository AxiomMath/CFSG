module

public import Certificates.Kernel.J2Fix280.CheckA
public import Certificates.Kernel.J2Fix280.CheckBC
public import CFSG.Certificates.Kernel.Item434.PkSound
public import Certificates.Data.J2Fix280
public import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.RankThree.F2Perm
import Certificates.Kernel.LocalComp.Fi24TwoB.L15027
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.Sporadic.Fi22.C3151A
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import Certificates.Kernel.Sporadic.Fi22.C2068
import CFSG.Certificates.Kernel.Spor.ConjTreeSound
import Certificates.Kernel.Sporadic.Fi22.C3151

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Fix280

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Item434
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.J2Residue.C280
open CFSG.KC.B3S3K (cm)

theorem get_all {a : Array ℕ} {n P : ℕ} (ha : a = unpack n 9 P)
    (hP0 : Nat.beq (Nat.shiftRight P (n * 9)) 0 = true) (i : ℕ) : a[i]! = tg P i := by
  subst ha
  have hP : P < 2 ^ (n * 9) := Nat.lt_of_div_eq_zero (Nat.two_pow_pos _)
    (by rw [← Nat.shiftRight_eq_div_pow]; exact Nat.eq_of_beq_eq_true hP0)
  by_cases h : i < n
  · exact CFSG.KC.Misc.PairCount.unpack_get h
  · rw [getElem!_neg _ i (by unfold unpack; rw [Array.size_ofFn]; exact h)]
    have hw : n * 9 ≤ 9 * i := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left 9 (by omega)
    have e : Nat.shiftRight P (Nat.mul 9 i) = 0 := by
      have e1 : Nat.shiftRight P (Nat.mul 9 i) = P >>> (9 * i) := rfl
      rw [e1, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num) hw))
    unfold tg pg
    rw [e]
    exact (Nat.zero_and _).symm

theorem tA_get (i : ℕ) : tA[i]! = tg TA i :=
  get_all (n := 280) (arrBind_sound (by quickRfl)) (by quickRfl) i

theorem tB_get (i : ℕ) : tB[i]! = tg TB i :=
  get_all (n := 280) (arrBind_sound (by quickRfl)) (by quickRfl) i

theorem tZ_get (i : ℕ) : tZ[i]! = tg TZ i :=
  get_all (n := 280) (arrBind_sound (by quickRfl)) (by quickRfl) i

theorem reps_get (i : ℕ) : reps[i]! = tg REPS i :=
  get_all (n := 3) (arrBind_sound (by quickRfl)) (by quickRfl) i

theorem cls_get (i : ℕ) : cls[i]! = tg CLS i :=
  get_all (n := 280) (arrBind_sound (by quickRfl)) (by quickRfl) i

theorem uIdx_get (i : ℕ) : uIdx[i]! = tg UIDX i :=
  get_all (n := 280) (arrBind_sound (by quickRfl)) (by quickRfl) i

theorem tabOf_get (k j : ℕ) : (tabOf k)[j]! = tg (if k = 0 then TA else TB) j := by
  unfold tabOf
  split
  · exact tA_get j
  · exact tB_get j

theorem tab_eq (u : List ℕ) (i : ℕ) : tab u i = tabK u i := by
  induction u with
  | nil => rfl
  | cons k u ih =>
    unfold tab tabK at *
    rw [List.foldr_cons, List.foldr_cons, ih, tabOf_get]

theorem tab_eq' : tab = tabK := funext fun u => funext fun i => tab_eq u i

theorem uOf_eq (j : ℕ) : uOf j = uOfK j := by
  unfold uOf uOfK
  rw [uIdx_get]

theorem rel_eq (c : ℕ) : rel c = relK c := by
  unfold rel relK
  rw [reps_get, tZ_get, tZ_get]

theorem relMu_eq (m : List Bool) (c : ℕ) : relMu m c = relMuK m c := by
  unfold relMu relMuK
  rw [rel_eq]

theorem combList_eq (m : List Bool) (ts : List (ℕ × ℕ)) : combList m ts = combListK m ts := by
  unfold combList combListK
  simp only [cls_get, relMu_eq, uOf_eq, tab_eq']

theorem checkB_eq : checkB () = checkBK := by
  unfold checkB checkBK
  simp only [reps_get, tZ_get, cls_get, combList_eq]

theorem checkC_eq : checkC () = checkCK := by
  unfold checkC checkCK
  simp only [tZ_get, cls_get, uOf_eq, rel_eq, tab_eq']

theorem hab (k : ℕ) (hk : k < 2) : CFSG.ComponentClassification.J2Cover.autStrong[k]! =
    unpack 315 9 (AB k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem pkG (k : ℕ) : Pk 315 9 (genA k) (gK k) := by
  unfold genA gK
  split
  · exact ⟨hab 0 (by norm_num), c111603P.1⟩
  · exact ⟨hab 1 (by norm_num), c111603P.2.1⟩

theorem pkZ : Pk 315 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr Z :=
  ⟨arrBind_sound (by quickRfl), c111603P.2.2⟩

theorem pkW (w : List ℕ) :
    Pk 315 9 (CFSG.RankThree.PartTwo.J2Residue.C280.wordA w) (wK w) := by
  induction w with
  | nil => exact pk_id c111603W
  | cons k w ih =>
    unfold CFSG.RankThree.PartTwo.J2Residue.C280.wordA wK at *
    rw [List.foldr_cons, List.foldr_cons]
    exact pk_comp c111603W (pkG k) ih

theorem rowT_true {i : ℕ} (hi : i < 280) : rowT i = true := by
  obtain ⟨c, hc, j, hj, rfl⟩ : ∃ c < 7, ∃ j < 40, i = j + 40 * c :=
    ⟨i / 40, by omega, i % 40, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases c
  · exact CFSG.KS.Raw.Orb.allN_iff.1 c111603A0 j hj
  · exact CFSG.KS.Raw.Orb.allN_iff.1 c111603A1 j hj
  · exact CFSG.KS.Raw.Orb.allN_iff.1 c111603A2 j hj
  · exact CFSG.KS.Raw.Orb.allN_iff.1 c111603A3 j hj
  · exact CFSG.KS.Raw.Orb.allN_iff.1 c111603A4 j hj
  · exact CFSG.KS.Raw.Orb.allN_iff.1 c111603A5 j hj
  · exact CFSG.KS.Raw.Orb.allN_iff.1 c111603A6 j hj

theorem validA_pk {a : Array ℕ} {p : ℕ} (ha : Pk 315 9 a p) : validA 315 a = true :=
  isInvA_pk ha

theorem gI_eq (k : ℕ) : gI k = pinvS 315 9 (mask 9) (gK k) := by
  unfold gI gK
  split
  · exact (Nat.eq_of_beq_eq_true c111603I.1).symm
  · exact (Nat.eq_of_beq_eq_true c111603I.2.1).symm

theorem ZI_eq : ZI = pinvS 315 9 (mask 9) Z := (Nat.eq_of_beq_eq_true c111603I.2.2).symm

theorem wcode_nil : wcode [] = 1 := rfl

theorem wcode_cons (k : ℕ) (w : List ℕ) : wcode (k :: w) = 2 * wcode w + k := rfl

theorem wcode_pos : ∀ w : List ℕ, 0 < wcode w
  | [] => Nat.one_pos
  | k :: w => by
    rw [wcode_cons]
    have := wcode_pos w
    omega

theorem wcode_inj : ∀ (w v : List ℕ), (∀ k ∈ w, k < 2) → (∀ k ∈ v, k < 2) →
    wcode w = wcode v → w = v
  | [], [], _, _, _ => rfl
  | [], j :: v, _, _, h => by
    rw [wcode_cons, wcode_nil] at h
    have := wcode_pos v
    omega
  | k :: w, [], _, _, h => by
    rw [wcode_cons, wcode_nil] at h
    have := wcode_pos w
    omega
  | k :: w, j :: v, hw, hv, h => by
    rw [wcode_cons, wcode_cons] at h
    have hk := hw k List.mem_cons_self
    have hj := hv j List.mem_cons_self
    have e1 : k = j := by omega
    have e2 : wcode w = wcode v := by omega
    rw [e1, wcode_inj w v (fun x hx => hw x (List.mem_cons_of_mem _ hx))
      (fun x hx => hv x (List.mem_cons_of_mem _ hx)) e2]

theorem wcChk_get : ∀ (ws : List (List ℕ)) (j : ℕ), wcChk ws j = true →
    ∀ i < ws.length, wcode ws[i]! = wcT (j + i) ∧ ∀ k ∈ ws[i]!, k < 2
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | w :: ws, j, h, i, hi => by
    have h' : (Nat.beq (wcode w) (wcT j) && w.all (fun k => Nat.blt k 2) &&
        wcChk ws (Nat.succ j)) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    cases i with
    | zero =>
      rw [List.getElem!_cons_zero]
      exact ⟨Nat.eq_of_beq_eq_true h1,
        fun k hk => Nat.le_of_ble_eq_true (List.all_eq_true.1 h2 k hk)⟩
    | succ i =>
      rw [List.getElem!_cons_succ]
      have := wcChk_get ws (Nat.succ j) h3 i (by simp only [List.length_cons] at hi; omega)
      rw [Nat.succ_add] at this
      exact this

theorem words_get {i : ℕ} (hi : i < 280) :
    wcode words[i]! = wcT i ∧ ∀ k ∈ words[i]!, k < 2 := by
  have hs : words.size = 280 := Nat.eq_of_beq_eq_true c111603Wn
  have e : words[i]! = words.toList[i]! := by
    rw [getElem!_pos words i (by omega),
      getElem!_pos words.toList i (by rw [Array.length_toList]; omega), Array.getElem_toList]
  rw [e]
  have h := wcChk_get words.toList 0 c111603Wc i (by rw [Array.length_toList]; omega)
  rw [Nat.zero_add] at h
  exact h

theorem cj315_comp {s e x : Array ℕ} {S E X : Equiv.Perm (Fin 315)}
    (hs : CFSG.Monster.B.Co2.Rep 315 s S) (he : CFSG.Monster.B.Co2.Rep 315 e E)
    (hx : CFSG.Monster.B.Co2.Rep 315 x X) :
    CFSG.RankThree.Native.conjA 315 (CFSG.Monster.B.Co2.Native.compA 315 s e) x =
      CFSG.RankThree.Native.conjA 315 s (CFSG.RankThree.Native.conjA 315 e x) :=
  CertificateChecks.KernelLC.Fi24B.conjA_compA hs he hx

theorem rep_pk {a : Array ℕ} {p : ℕ} (ha : Pk 315 9 a p) :
    CFSG.Monster.B.Co2.Rep 315 a (CFSG.Monster.B.Co2.permOfArr 315 a) :=
  rep_of_validA (validA_pk ha)

theorem pkY : ∀ i, i < 280 → Pk 315 9 (conjY i) (YT i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h0 : i = 0
    · subst h0
      rw [Nat.eq_of_beq_eq_true c111603Y0]
      exact pk_conjA c111603W (pkW _) pkZ
    · have h := rowT_true hi
      unfold rowT at h
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨ht, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
      rcases ht with ht | ⟨⟨⟨hp, hk⟩, hc⟩, hy⟩
      · exact absurd (Nat.eq_of_beq_eq_true ht) h0
      · have hp' : tg PAR i < i := Nat.le_of_ble_eq_true hp
        have hk' : tg LET i < 2 := Nat.le_of_ble_eq_true hk
        have hc' : wcT i = 2 * wcT (tg PAR i) + tg LET i := Nat.eq_of_beq_eq_true hc
        have hw := words_get hi
        have hwp := words_get (i := tg PAR i) (by omega)
        have hword : words[i]! = tg LET i :: words[tg PAR i]! :=
          wcode_inj _ _ hw.2 (List.forall_mem_cons.2 ⟨hk', hwp.2⟩)
            (by rw [hw.1, wcode_cons, hwp.1]; exact hc')
        have e1 : conjY i = CFSG.RankThree.Native.conjA 315
            (CFSG.RankThree.PartTwo.J2Residue.C280.wordA (tg LET i :: words[tg PAR i]!))
            CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr := by
          unfold conjY
          rw [hword]
        have e3 : CFSG.RankThree.PartTwo.J2Residue.C280.wordA (tg LET i :: words[tg PAR i]!) =
            CFSG.Monster.B.Co2.Native.compA 315 (genA (tg LET i))
              (CFSG.RankThree.PartTwo.J2Residue.C280.wordA words[tg PAR i]!) := rfl
        have e4 : conjY (tg PAR i) = CFSG.RankThree.Native.conjA 315
            (CFSG.RankThree.PartTwo.J2Residue.C280.wordA words[tg PAR i]!)
            CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr := rfl
        have e2 : conjY i = CFSG.RankThree.Native.conjA 315 (genA (tg LET i)) (conjY (tg PAR i)) := by
          rw [e1, e3, e4]
          exact cj315_comp (rep_pk (pkG _)) (rep_pk (pkW _)) (rep_pk pkZ)
        rw [e2, Nat.eq_of_beq_eq_true hy, gI_eq]
        exact pk_conjA c111603W (pkG _) (ih _ hp' (by omega))

theorem sameLine_pk {t y : Array ℕ} {p q : ℕ} (ht : Pk 315 9 t p) (hy : Pk 315 9 y q) :
    sameLine t y = sameK p q := by
  unfold sameLine sameK
  rw [eqA_pk c111603W ht hy, eqA_pk c111603W ht (pk_comp c111603W hy hy)]

theorem ys_get {i : ℕ} (hi : i < 280) :
    (Array.ofFn (n := 280) fun i => conjY i.val)[i]! = conjY i := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem checkA_true : checkA () = true := by
  unfold checkA
  simp only
  rw [validA_pk (pkG 0), validA_pk (pkG 1), validA_pk pkZ, Bool.true_and, Bool.true_and,
    Bool.true_and]
  refine List.all_eq_true.2 fun i hi => ?_
  rw [List.mem_range] at hi
  have h := rowT_true hi
  unfold rowT at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hA⟩, hB⟩, hZ⟩, sA⟩, sB⟩, sZ⟩ := h
  rw [gI_eq] at sA sB
  rw [ZI_eq] at sZ
  have hA' : tg TA i < 280 := Nat.le_of_ble_eq_true hA
  have hB' : tg TB i < 280 := Nat.le_of_ble_eq_true hB
  have hZ' : tg TZ i < 280 := Nat.le_of_ble_eq_true hZ
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [tA_get, tB_get, tZ_get, ys_get hi, ys_get hA', ys_get hB', ys_get hZ']
  refine ⟨⟨⟨⟨⟨⟨validA_pk (pkW _), hA'⟩, hB'⟩, hZ'⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [sameLine_pk (pk_conjA c111603W (pkG 0) (pkY i hi)) (pkY _ hA')]
    exact sA
  · rw [sameLine_pk (pk_conjA c111603W (pkG 1) (pkY i hi)) (pkY _ hB')]
    exact sB
  · rw [sameLine_pk (pk_conjA c111603W pkZ (pkY i hi)) (pkY _ hZ')]
    exact sZ

open Certificates in
theorem facts111603 : CFSG.RankThree.PartTwo.J2Residue.C280.checkA () = true ∧
    CFSG.RankThree.PartTwo.J2Residue.C280.checkB () = true ∧
    CFSG.RankThree.PartTwo.J2Residue.C280.checkC () = true :=
  ⟨checkA_true, checkB_eq ▸ c111603B, checkC_eq ▸ c111603C⟩

end CertificateChecks.KernelJ2Fix280

end
