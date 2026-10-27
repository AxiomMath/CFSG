module

public import Certificates.Kernel.OmegaEight.Roots127KB
public import CFSG.Certificates.Kernel.O8RootsSound
public import CFSG.Certificates.Kernel.O8RootsReduce
import CFSG.Certificates.Kernel.PackSetSound
public import Certificates.Kernel.OmegaEight.Bridge3009

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

private theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem bIfT {c t e : Bool} (hc : c = true) :
    Bool.rec (motive := fun _ => Bool) e t c = t := by
  subst hc; rfl

private theorem bIfF {c t e : Bool} (hc : c = false) :
    Bool.rec (motive := fun _ => Bool) e t c = e := by
  subst hc; rfl

private theorem nIfT {c : Bool} {t e : Nat} (hc : c = true) :
    Bool.rec (motive := fun _ => Nat) e t c = t := by
  subst hc; rfl

private theorem nIfF {c : Bool} {t e : Nat} (hc : c = false) :
    Bool.rec (motive := fun _ => Nat) e t c = e := by
  subst hc; rfl

private theorem bImp {c t : Bool} (h : Bool.rec (motive := fun _ => Bool) true t c = true)
    (hc : c = true) : t = true := by
  subst hc; exact h

private theorem beqT {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact Nat.beq_refl a

private theorem beqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

private theorem ne_of_bIf {a b : Nat}
    (h : Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b) = true) : a ≠ b := fun e => by
  rw [beqT e] at h; exact absurd h (by decide)

private theorem fldE (q o r : Nat) :
    Nat.land (Nat.shiftRight q o) (2 ^ r - 1) = q / 2 ^ o % 2 ^ r := by
  change (q >>> o) &&& (2 ^ r - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem saAtK_saCodes (i : Nat) : saAtK saCodes i = saMat i := fldE saCodes (64 * i) 64

private theorem ix13_yIdx (k : Nat) : ix13 yIdxT k = yIdx k := fldE yIdxT (13 * k) 13


private theorem mpowK_succ (x m : Nat) : mpowK x (m + 1) = matMulM (mpowK x m) x := by
  change strictN (mpowK x m) (fun a => matMulK a x) = _
  rw [sN, matMulK_eq]

section Acts


private theorem acts_mpowK {g : Equiv.Perm (Fin 360)} {x : Nat} (hg : Acts g x) :
    ∀ m, Acts (g ^ m) (mpowK x m) ∧ mpowK x m < 2 ^ 64
  | 0 => by
    change Acts (g ^ 0) CFSG.KC.O8.idK ∧ CFSG.KC.O8.idK < 2 ^ 64
    rw [idK_eq, pow_zero]
    exact ⟨acts_one, idCode_lt⟩
  | m + 1 => by
    rw [mpowK_succ, pow_succ]
    exact ⟨acts_mul (acts_mpowK hg m).1 hg, matMulM_lt _ _⟩

private theorem eqΩ {u v : Equiv.Perm (Fin 360)} (hu : u ∈ omegaT) (hv : v ∈ omegaT) {M : ℕ}
    (au : Acts u M) (av : Acts v M) : u = v := by
  have h : omegaRes ⟨u, hu⟩ = omegaRes ⟨v, hv⟩ := by
    refine Equiv.ext fun j => Fin.ext ?_
    rw [omegaRes_apply_val, omegaRes_apply_val]
    exact (au j j.2).2.trans (av j j.2).2.symm
  exact congrArg Subtype.val (omegaRes_injective h)

private theorem rep_AP {j : ℕ} (hj : j < 10) : Rep 360 (unpack 360 9 (AP.S j)) (gen j) := by
  rw [← gen_get hj]
  exact rep_gen hj

private theorem rep_pc {p q : ℕ} {g h : Equiv.Perm (Fin 360)} (hp : cn p = true)
    (hq : cn q = true) (rp : Rep 360 (unpack 360 9 p) g) (rq : Rep 360 (unpack 360 9 q) h) :
    Rep 360 (unpack 360 9 (pc p q)) (g * h) := by
  rw [← compA_pc hp hq]
  exact rep_compA rp rq

private theorem rep_main {t : ℕ} (ht : t < 5) : Rep 360 (unpack 360 9 (mainK t)) (mainPerm t) := by
  rw [← (main_ok ht).1]
  exact (mainPerm_spec ht).1

private theorem main0_eq : mainPerm 0 = repPerm 10 := by
  rw [mainPerm, repPerm, mainArrs_getD (by norm_num), repArrs_getD (by norm_num)]
  rfl

private theorem acts_rep {k : ℕ} (hk : k < 38) :
    Acts (repPerm k) (saAtK (ycK saCodes yIdxT) k) := by
  have h := kY127
  rw [sB] at h
  rw [Nat.eq_of_beq_eq_true (allN_spec h k hk), ix13_yIdx, saAtK_saCodes]
  exact acts_of_rep (repPerm_spec hk).1 (sa_facts.reps k hk).2

private theorem look127 {k : ℕ} (hk : k < 38) :
    (repTypes.getD k 0 = 1 → lookL (tyLK (ycK saCodes yIdxT) r127Ty 1)
      (saAtK (ycK saCodes yIdxT) k) = k + 1) ∧
    (repTypes.getD k 0 = 2 → lookL (tyLK (ycK saCodes yIdxT) r127Ty 2)
      (saAtK (ycK saCodes yIdxT) k) = k + 1) := by
  have h := kLook127
  unfold r127Look at h
  rw [sB, sB, sB] at h
  have h' := allN_spec h k hk
  rw [sB] at h'
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
  exact ⟨fun e => Nat.eq_of_beq_eq_true (bImp h1 (beqT e)),
    fun e => Nat.eq_of_beq_eq_true (bImp h2 (beqT e))⟩

private theorem sq_rep {k : ℕ} (hk : k < 38) : repPerm k * repPerm k = 1 := by
  rw [← pow_two, ← orderOf_repPerm hk, pow_orderOf_eq_one]

private theorem sq_code {i k : ℕ} (hi : i < 8192) (hk : k < 38)
    (h : saElt i * saElt i = repPerm k) :
    matMulK (saAtK saCodes i) (saAtK saCodes i) = saAtK (ycK saCodes yIdxT) k := by
  have a := (saElt_spec sa_facts i hi).2
  have a2 := acts_mul a a
  rw [h] at a2
  rw [saAtK_saCodes, matMulK_eq]
  exact acts_unique sa_facts (matMulM_lt _ _) (by
    rw [show saAtK (ycK saCodes yIdxT) k = _ from rfl]
    exact Nat.and_lt_two_pow _ (by norm_num)) a2 (acts_rep hk)

private theorem par_one {i : ℕ} (hi : i < 8192) (hO : saElt i ∉ omegaT) :
    parK saParT saLabT i = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (parK_le i) with h | h
  · exact absurd ((parK_spec i hi).2 h) hO
  · exact h

@[expose] noncomputable def r127Ws : List (Nat × Nat × Nat) :=
  r127W.map fun w => (r127M (wO w.1), r127M (pinv (wO w.1)), w.2)

private theorem scanBlk {b : Nat} (h : r127Scan b = true) : ∀ l < 1024,
    scanAt saCodes saParT saLabT (tyLK (ycK saCodes yIdxT) r127Ty 2)
      (saAtK (ycK saCodes yIdxT) 10) r127Ws (Nat.add b l) = true := by
  unfold r127Scan r127Wit at h
  simp only [sB] at h
  exact allBlk_spec h

private theorem scanAll {i : ℕ} (hi : i < 8192) :
    scanAt saCodes saParT saLabT (tyLK (ycK saCodes yIdxT) r127Ty 2)
      (saAtK (ycK saCodes yIdxT) 10) r127Ws i = true := by
  obtain ⟨q, l, hl, rfl⟩ : ∃ q l, l < 1024 ∧ i = Nat.add (1024 * q) l :=
    ⟨i / 1024, i % 1024, Nat.mod_lt _ (by norm_num), by change i = 1024 * (i / 1024) + i % 1024; omega⟩
  have hq : q < 8 := by change 1024 * q + l < 8192 at hi; omega
  interval_cases q
  · exact scanBlk kScan127_0 l hl
  · exact scanBlk kScan127_1 l hl
  · exact scanBlk kScan127_2 l hl
  · exact scanBlk kScan127_3 l hl
  · exact scanBlk kScan127_4 l hl
  · exact scanBlk kScan127_5 l hl
  · exact scanBlk kScan127_6 l hl
  · exact scanBlk kScan127_7 l hl

private theorem scanAt_spec {SC PT LT L2 X : Nat} {W : List (Nat × Nat × Nat)} {i : Nat}
    (h : scanAt SC PT LT L2 X W i = true) (hp : parK PT LT i = 1) :
    lookL L2 (matMulK (saAtK SC i) (saAtK SC i)) = 0 ∧
      (matMulK (saAtK SC i) (saAtK SC i) = X → critM X (saAtK SC i) W = true) := by
  unfold scanAt at h
  rw [bIfT (beqT hp), sB, sB] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, fun e => bImp h2 (beqT e)⟩

private noncomputable def critG (X J : Nat) (w : Nat × Nat × Nat) : Nat :=
  mpowK (matMulK (matMulK (matMulK (matMulK J X) w.1) J) w.2.1) w.2.2

private noncomputable def critStep (Ji J : Nat) (w : Nat × Nat × Nat)
    (_ : List (Nat × Nat × Nat)) (ih : Bool) : Bool :=
  strictB (mpowK (matMulK (matMulK (matMulK Ji w.1) J) w.2.1) w.2.2) fun g =>
    bIf(bAnd(Nat.beq (matMulK g (matMulK g g)) idK, bIf(Nat.beq g idK, false, true)), true, ih)

private theorem critM_eq (X J : Nat) (W : List (Nat × Nat × Nat)) :
    critM X J W = List.rec false (critStep (matMulK J X) J) W := by
  unfold critM
  rw [sB]
  rfl

private theorem critM_spec {X J : Nat} {W : List (Nat × Nat × Nat)} (h : critM X J W = true) :
    ∃ w ∈ W, matMulK (critG X J w) (matMulK (critG X J w) (critG X J w)) = CFSG.KC.O8.idK ∧
      critG X J w ≠ CFSG.KC.O8.idK := by
  rw [critM_eq] at h
  induction W with
  | nil => exact absurd h Bool.false_ne_true
  | cons w W ih =>
    change critStep (matMulK J X) J w W (List.rec false (critStep (matMulK J X) J) W) = true at h
    unfold critStep at h
    rw [sB] at h
    have hG : critG X J w =
        mpowK (matMulK (matMulK (matMulK (matMulK J X) w.1) J) w.2.1) w.2.2 := rfl
    generalize mpowK (matMulK (matMulK (matMulK (matMulK J X) w.1) J) w.2.1) w.2.2 = G at h hG
    cases hc : bAnd(Nat.beq (matMulK G (matMulK G G)) CFSG.KC.O8.idK,
        bIf(Nat.beq G CFSG.KC.O8.idK, false, true))
    · rw [hc] at h
      obtain ⟨w', hw', hw''⟩ := ih h
      exact ⟨w', List.mem_cons_of_mem _ hw', hw''⟩
    · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hc
      refine ⟨w, by simp, ?_⟩
      rw [hG]
      exact ⟨Nat.eq_of_beq_eq_true h1, ne_of_bIf h2⟩

theorem cent127 : ∀ s ∈ sylowT, s * mainPerm 0 = mainPerm 0 * s := by
  have hC := kStrC
  simp only [bAnd_iff] at hC
  have hc : ∀ j < 10, cn (AP.S j) = true := allN_spec hC.1
  have hm := (main_ok (i := 0) (by norm_num)).2.1
  have hle : sylowT ≤ Subgroup.centralizer ({mainPerm 0} : Set (Equiv.Perm (Fin 360))) := by
    rw [sylowT_eq, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh]
    have hx := sylowIdx_lt hl
    have e := Nat.eq_of_beq_eq_true (allN_spec kCent127 l hl)
    have r1 := rep_pc (hc _ hx) hm (rep_AP hx) (rep_main (t := 0) (by norm_num))
    have r2 := rep_pc hm (hc _ hx) (rep_main (t := 0) (by norm_num)) (rep_AP hx)
    rw [e] at r1
    exact (r1.unique r2).symm
  intro s hs
  exact (Subgroup.mem_centralizer_iff.1 (hle hs) (mainPerm 0) rfl).symm

theorem ord127 : ∀ i < 3, mainPerm i * mainPerm i = 1 ∧ mainPerm i ≠ 1 := by
  have key : ∀ k < 38, mainPerm (repTypes.getD k 0) * mainPerm (repTypes.getD k 0) = 1 ∧
      mainPerm (repTypes.getD k 0) ≠ 1 := by
    intro k hk
    have e := conj_mainPerm hk
    set c := conjPerm k
    have ex : mainPerm (repTypes.getD k 0) = c⁻¹ * repPerm k * c := by rw [← e]; group
    rw [ex]
    refine ⟨?_, fun h => ?_⟩
    · calc c⁻¹ * repPerm k * c * (c⁻¹ * repPerm k * c) = c⁻¹ * (repPerm k * repPerm k) * c := by
            group
        _ = 1 := by rw [sq_rep hk]; group
    · have h1 : repPerm k = 1 := by
        calc repPerm k = c * (c⁻¹ * repPerm k * c) * c⁻¹ := by group
          _ = 1 := by rw [h]; group
      have := orderOf_repPerm hk
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
  intro i hi
  interval_cases i
  · exact key 10 (by norm_num)
  · exact key 3 (by norm_num)
  · exact key 12 (by norm_num)

private theorem fixF_eq (P : Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p ih => Nat.add ih (nIf(Nat.beq (pg (nat_lit 9) (nat_lit 511) P p) p, nat_lit 1,
      nat_lit 0))) n = ∑ p ∈ Finset.range n, if pg 9 511 P p = p then 1 else 0
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← fixF_eq P n]
    change Nat.add _ _ = _
    by_cases h : pg 9 511 P n = n
    · rw [nIfT (beqT h), if_pos h]
    · rw [nIfF (beqF h), if_neg h]

private theorem fix360K_eq {P : Nat} {g : Equiv.Perm (Fin 360)} (h : Rep 360 (unpack 360 9 P) g) :
    fix360K P = ∑ q : Fin 360, if g q = q then 1 else 0 := by
  unfold fix360K
  refine (fixF_eq P 360).trans ?_
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun q _ => ?_
  have e : pg 9 511 P q = (g q : ℕ) := by
    rw [← h.apply q.2]
    exact (at9_eq q.2).symm
  simp only [e, Fin.val_inj]

private theorem fix_conj (g x : Equiv.Perm (Fin 360)) :
    (∑ q : Fin 360, if (g * x * g⁻¹) q = q then 1 else 0) =
      ∑ q : Fin 360, if x q = q then 1 else 0 := by
  refine Fintype.sum_equiv (g⁻¹ : Equiv.Perm (Fin 360)) _ _ fun q => ?_
  have e : (g * x * g⁻¹) q = q ↔ x (g⁻¹ q) = g⁻¹ q := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact Equiv.Perm.eq_inv_iff_eq.symm
  by_cases h : x (g⁻¹ q) = g⁻¹ q
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h]

theorem type127 : ∀ t < 5, ∀ i < 3, ∀ g : Equiv.Perm (Fin 360),
    g * mainPerm i * g⁻¹ = mainPerm t → t = i := by
  intro t ht i hi g hg
  have hf : ∀ s < 5, (∑ q : Fin 360, if mainPerm s q = q then 1 else 0) = r127Fix.getD s 0 :=
    fun s hs => by
      rw [← fix360K_eq (rep_main hs)]
      exact Nat.eq_of_beq_eq_true (allN_spec kFix127 s hs)
  have e := fix_conj g (mainPerm i)
  rw [hg, hf t ht, hf i (by omega)] at e
  interval_cases t <;> interval_cases i <;> first | rfl | exact absurd e (by decide)

theorem scan127 : ∀ k < 38, repTypes.getD k 0 = 2 → ∀ j ∈ sylowT, j ∉ omegaT →
    j * j ≠ repPerm k := by
  intro k hk ht j hj hjO hjj
  obtain ⟨i, hi, rfl⟩ := exists_saElt sa_facts hj
  have h := (scanAt_spec (scanAll hi) (par_one hi hjO)).1
  rw [sq_code hi hk hjj, (look127 hk).2 ht] at h
  exact Nat.succ_ne_zero _ h

theorem crit127 : ∀ j ∈ sylowT, j ∉ omegaT → j * j = mainPerm 0 →
    ∃ c ∈ omegaT, c * mainPerm 0 = mainPerm 0 * c ∧ ∃ k : ℕ,
      (j⁻¹ * c * j * c⁻¹) ^ k ≠ 1 ∧ ((j⁻¹ * c * j * c⁻¹) ^ k) ^ 3 = 1 := by
  intro j hj hjO hjj
  obtain ⟨i, hi, rfl⟩ := exists_saElt sa_facts hj
  have hsq := sq_code hi (k := 10) (by norm_num) (by rw [hjj, main0_eq])
  have hcrit := (scanAt_spec (scanAll hi) (par_one hi hjO)).2 hsq
  obtain ⟨w, hw, hg3, hg1⟩ := critM_spec hcrit
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
  simp only [critG] at hg3 hg1
  have hwit := List.all_eq_true.1 kWit127 p hp
  simp only [bAnd_iff, sB] at hwit
  obtain ⟨hlet, hcn, hpm, hcni, hcomm, hac, haci⟩ := hwit
  have hlo : lettersOK 17 p.1 = true := by
    simp only [r127W, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> decide
  obtain ⟨hcr, hcm⟩ := omegaW_spec hlo
  set c := permOfArr 360 (omegaW p.1)
  rw [omegaW_eq hlet] at hcr
  have hci : Rep 360 (unpack 360 9 (pinv (wO p.1))) c⁻¹ := by
    rw [← invCand_pinv hpm]
    exact rep_inv_of_isInvA hcr (isInvA_of hpm)
  have aC : Acts c (r127M (wO p.1)) := acts_of_rep hcr (acts_of hac)
  have aD : Acts c⁻¹ (r127M (pinv (wO p.1))) := acts_of_rep hci (acts_of haci)
  have hm := (main_ok (i := 0) (by norm_num)).2.1
  have hcx : c * mainPerm 0 = mainPerm 0 * c := by
    have r1 := rep_pc hcn hm hcr (rep_main (t := 0) (by norm_num))
    rw [Nat.eq_of_beq_eq_true hcomm] at r1
    exact r1.unique (rep_pc hm hcn (rep_main (t := 0) (by norm_num)) hcr)
  set j := saElt i
  have aJ : Acts j (saMat i) := (saElt_spec sa_facts i hi).2
  have aX : Acts (mainPerm 0) (saAtK (ycK saCodes yIdxT) 10) := by
    rw [main0_eq]
    exact acts_rep (by norm_num)
  have hx2 := (ord127 0 (by norm_num)).1
  have hjinv : j⁻¹ = j * mainPerm 0 :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hjj, hx2])
  have aB : Acts (j⁻¹ * c * j * c⁻¹) (matMulK (matMulK (matMulK (matMulK (saAtK saCodes i)
      (saAtK (ycK saCodes yIdxT) 10)) (r127M (wO p.1))) (saAtK saCodes i))
      (r127M (pinv (wO p.1)))) := by
    rw [matMulK_eq, matMulK_eq, matMulK_eq, matMulK_eq, saAtK_saCodes, hjinv]
    exact acts_mul (acts_mul (acts_mul (acts_mul aJ aX) aC) aJ) aD
  obtain ⟨aG, hlt⟩ := acts_mpowK aB p.2
  have hjA : j⁻¹ ∈ autT := autT.inv_mem (sylowT_le_autT hj)
  have hgm : (j⁻¹ * c * j * c⁻¹) ^ p.2 ∈ omegaT := by
    refine pow_mem (mul_mem ?_ (inv_mem hcm)) _
    have := (conj_mem_omegaT hjA).1 hcm
    rwa [inv_inv] at this
  refine ⟨c, hcm, hcx, p.2, fun h1 => hg1 ?_, ?_⟩
  · rw [h1] at aG
    rw [idK_eq]
    exact acts_unique sa_facts hlt idCode_lt aG acts_one
  · have a3 := acts_mul aG (acts_mul aG aG)
    rw [← matMulK_eq, ← matMulK_eq, hg3, idK_eq] at a3
    have e3 : ((j⁻¹ * c * j * c⁻¹) ^ p.2) ^ 3 = (j⁻¹ * c * j * c⁻¹) ^ p.2 *
        ((j⁻¹ * c * j * c⁻¹) ^ p.2 * (j⁻¹ * c * j * c⁻¹) ^ p.2) := by
      rw [pow_succ, pow_two, mul_assoc]
    rw [e3]
    exact eqΩ (mul_mem hgm (mul_mem hgm hgm)) (one_mem _) a3 acts_one

private noncomputable def recAllF (n R : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih R => bIf(Nat.beq R (nat_lit 0), true,
      bAnd(f (Nat.land R (nat_lit 2097151)), strictB (Nat.shiftRight R (nat_lit 21)) ih))) n R

private theorem shift_or {a r : Nat} (hr : r < 2 ^ 21) :
    Nat.lor (Nat.shiftLeft a 21) r = a * 2 ^ 21 + r := by
  change a <<< 21 ||| r = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt hr, Nat.shiftLeft_eq]

private theorem recAllF_cons {n a r : Nat} {f : Nat → Bool} (h0 : 0 < r) (hr : r < 2 ^ 21)
    (h : recAllF (n + 1) (Nat.lor (Nat.shiftLeft a 21) r) f = true) :
    f r = true ∧ recAllF n a f = true := by
  change Bool.rec (motive := fun _ => Bool)
    (bAnd(f (Nat.land (Nat.lor (Nat.shiftLeft a 21) r) 2097151),
      strictB (Nat.shiftRight (Nat.lor (Nat.shiftLeft a 21) r) 21) fun R => recAllF n R f)) true
    (Nat.beq (Nat.lor (Nat.shiftLeft a 21) r) 0) = true at h
  rw [shift_or hr, bIfF (beqF (by omega)), sB] at h
  have e1 : Nat.land (a * 2 ^ 21 + r) 2097151 = r := by
    change (a * 2 ^ 21 + r) &&& (2 ^ 21 - 1) = r
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hr]
  have e2 : Nat.shiftRight (a * 2 ^ 21 + r) 21 = a := by
    change (a * 2 ^ 21 + r) >>> 21 = a
    rw [Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [e1, e2] at h
  exact (bAnd_iff _ _).1 h

private theorem recAll_fold {g : Nat → Nat} {f : Nat → Bool} :
    ∀ (l : List Nat), (∀ i ∈ l, g i < 2 ^ 21) → ∀ n R, l.length ≤ n →
    R = l.foldr (fun i acc => strictN (g i) fun r =>
      nIf(Nat.beq r (nat_lit 0), acc, Nat.lor (Nat.shiftLeft acc (nat_lit 21)) r)) 0 →
    recAllF n R f = true → ∀ i ∈ l, g i ≠ 0 → f (g i) = true
  | [], _, _, _, _, _, _, i, hi, _ => absurd hi List.not_mem_nil
  | i :: l, hg, n, R, hn, hR, h, i', hi', hne => by
    have hl : ∀ k ∈ l, g k < 2 ^ 21 := fun k hk => hg k (List.mem_cons_of_mem _ hk)
    rw [hR, List.foldr_cons, sN] at h
    simp only [List.length_cons] at hn
    by_cases h0 : g i = 0
    · rw [nIfT (beqT h0)] at h
      rcases List.mem_cons.1 hi' with rfl | hi'
      · exact absurd h0 hne
      · exact recAll_fold l hl n _ (by omega) rfl h i' hi' hne
    · rw [nIfF (beqF h0)] at h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨hf, h'⟩ := recAllF_cons (Nat.pos_of_ne_zero h0) (hg i (by simp)) h
      rcases List.mem_cons.1 hi' with rfl | hi'
      · exact hf
      · exact recAll_fold l hl m _ (by omega) rfl h' i' hi' hne

private noncomputable def lkStep (s : Nat) : Nat → (Nat → Nat) → Nat → Nat := fun _ ih L =>
  nIf(Nat.beq L (nat_lit 0), nat_lit 0,
    nIf(Nat.beq (fld(L, nat_lit 6, nat_lit 18446744073709551615)) s,
      Nat.succ (Nat.land L (nat_lit 63)), strictN (Nat.shiftRight L (nat_lit 71)) ih))

private theorem lkF_le (s : Nat) : ∀ n L,
    Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0) (lkStep s) n L ≤ 64
  | 0, _ => Nat.zero_le _
  | n + 1, L => by
    change lkStep s n (Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0) (lkStep s) n) L
      ≤ 64
    unfold lkStep
    cases Nat.beq L (nat_lit 0)
    · cases Nat.beq (fld(L, nat_lit 6, nat_lit 18446744073709551615)) s
      · change strictN _ _ ≤ 64
        rw [sN]
        exact lkF_le s n _
      · exact Nat.succ_le_succ Nat.and_le_right
    · exact Nat.zero_le _

private theorem lookL_le (L s : Nat) : lookL L s ≤ 64 := lkF_le s 38 L

private theorem recAt_eq (SC PT LT L1 i : Nat) : recAt SC PT LT L1 i =
    if lookL L1 (matMulK (saAtK SC i) (saAtK SC i)) = 0 then 0 else
      1048576 + 128 * i + (2 * (lookL L1 (matMulK (saAtK SC i) (saAtK SC i)) - 1) +
        parK PT LT i) := by
  unfold recAt
  rw [sN, sN]
  by_cases h : lookL L1 (matMulK (saAtK SC i) (saAtK SC i)) = 0
  · rw [nIfT (beqT h), if_pos h]
  · rw [nIfF (beqF h), if_neg h]
    rfl

private theorem recAt_lt (SC PT LT L1 : Nat) {i : Nat} (hi : i < 8192) :
    recAt SC PT LT L1 i < 2 ^ 21 := by
  rw [recAt_eq]
  have h1 := lookL_le L1 (matMulK (saAtK SC i) (saAtK SC i))
  have h2 := parF_le PT LT 8192 i
  change _ ≤ 1 at h2
  split_ifs
  · positivity
  · change parK PT LT i ≤ 1 at h2
    omega

private theorem rec_fields {SC PT LT L1 i k : Nat} (hi : i < 8192) (hk : k < 38)
    (hl : lookL L1 (matMulK (saAtK SC i) (saAtK SC i)) = k + 1) :
    recAt SC PT LT L1 i ≠ 0 ∧ recP (recAt SC PT LT L1 i) = parK PT LT i ∧
      recR (recAt SC PT LT L1 i) = k ∧ recI (recAt SC PT LT L1 i) = i := by
  rw [recAt_eq, if_neg (by omega), hl]
  have hp : parK PT LT i ≤ 1 := parF_le PT LT 8192 i
  refine ⟨by omega, ?_, ?_, ?_⟩
  · change Nat.land _ 1 = _
    rw [show ∀ x : Nat, Nat.land x 1 = x % 2 from fun x => Nat.and_one_is_mod x]
    omega
  · change Nat.land (Nat.shiftRight _ 1) (2 ^ 6 - 1) = _
    rw [fldE]
    omega
  · change Nat.land (Nat.shiftRight _ 7) (2 ^ 13 - 1) = _
    rw [fldE]
    omega

private theorem recAll_eq (R : Nat) (f : Nat → Bool) : recAll R f = recAllF (nat_lit 8192) R f :=
  rfl

theorem pair127 : ∀ k < 38, repTypes.getD k 0 = 1 → ∀ j ∈ sylowT, j ∉ omegaT →
    j * j = repPerm k → ∀ u ∈ sylowT, u ∈ omegaT → u * u = repPerm k → j * u * j⁻¹ ≠ u⁻¹ := by
  intro k hk ht j hj hjO hjj u hu huO huu he
  obtain ⟨a, ha, rfl⟩ := exists_saElt sa_facts hj
  obtain ⟨b, hb, rfl⟩ := exists_saElt sa_facts hu
  have hP := kPair127
  unfold r127Pair at hP
  rw [sB, sB, sB] at hP
  unfold pairK at hP
  rw [recAll_eq] at hP
  have hR := CFSG.KC.Pack.foldN_eq (nat_lit 8192) (fun i acc =>
    strictN (recAt saCodes saParT saLabT (tyLK (ycK saCodes yIdxT) r127Ty 1) i) fun r =>
      nIf(Nat.beq r (nat_lit 0), acc, Nat.lor (Nat.shiftLeft acc (nat_lit 21)) r)) (nat_lit 0)
  have hbd : ∀ i ∈ List.range 8192,
      recAt saCodes saParT saLabT (tyLK (ycK saCodes yIdxT) r127Ty 1) i < 2 ^ 21 :=
    fun i hi => recAt_lt _ _ _ _ (List.mem_range.1 hi)
  obtain ⟨na, pa, rka, ia⟩ := rec_fields (PT := saParT) (LT := saLabT) ha hk
    ((sq_code ha hk hjj).symm ▸ (look127 hk).1 ht)
  obtain ⟨nb, pb, rkb, ib⟩ := rec_fields (PT := saParT) (LT := saLabT) hb hk
    ((sq_code hb hk huu).symm ▸ (look127 hk).1 ht)
  have ho := recAll_fold (List.range 8192) hbd 8192 _ (by simp) hR hP a (List.mem_range.2 ha) na
  beta_reduce at ho
  rw [pa, par_one ha hjO, bIfT (beqT rfl), sB, sB, sB, rka, ia, recAll_eq] at ho
  have hi := recAll_fold (List.range 8192) hbd 8192 _ (by simp) hR ho b (List.mem_range.2 hb) nb
  beta_reduce at hi
  rw [pb, (parK_spec b hb).1 huO, rkb, bIfT ((bAnd_iff _ _).2 ⟨beqT rfl, beqT rfl⟩), sB, ib] at hi
  have hne := ne_of_bIf hi
  apply hne
  have hy := sq_rep hk
  have hui : (saElt b)⁻¹ = saElt b * repPerm k :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, huu, hy])
  have e : saElt a * saElt b = saElt b * repPerm k * saElt a := by
    calc saElt a * saElt b = saElt a * saElt b * (saElt a)⁻¹ * saElt a := by group
      _ = saElt b * repPerm k * saElt a := by rw [he, hui]
  have aA := (saElt_spec sa_facts a ha).2
  have aB := (saElt_spec sa_facts b hb).2
  have a1 := acts_mul aA aB
  have a2 := acts_mul (acts_mul aB (acts_rep hk)) aA
  rw [← e] at a2
  rw [matMulK_eq, matMulK_eq, matMulK_eq, saAtK_saCodes, saAtK_saCodes]
  exact acts_unique sa_facts (matMulM_lt _ _) (matMulM_lt _ _) a1 a2

theorem outer_root127 {i : ℕ} (hi : i < 3) {j : Equiv.Perm (Fin 360)} (hjA : j ∈ autT)
    (hjO : j ∉ omegaT) (hjj : j * j = mainPerm i) :
    (∃ c ∈ omegaT, c * mainPerm i = mainPerm i * c ∧ ∃ k : ℕ,
        (j⁻¹ * c * j * c⁻¹) ^ k ≠ 1 ∧ ((j⁻¹ * c * j * c⁻¹) ^ k) ^ 3 = 1) ∨
      ∀ u ∈ omegaT, u * u = mainPerm i → j * u * j⁻¹ ≠ u⁻¹ :=
  outer_root_of cent127 crit127 pair127 scan127 type127 ord127 hi hjA hjO hjj

end Acts

end CertificateChecks.KernelO8

end
