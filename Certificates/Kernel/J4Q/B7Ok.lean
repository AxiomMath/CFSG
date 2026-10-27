module

public import Certificates.Kernel.J4Q.B7K
public import Certificates.Kernel.J4Q.VcOk
public import Certificates.Kernel.J4Q.C4004
public import CFSG.Certificates.Kernel.J4Q.RepB7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7W
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7InstInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Check
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Fix
public import CFSG.Sporadic.J4.QT2LocFixMain
public import CFSG.Sporadic.J4.QT2LocRadMain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.LQT.Syl CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.QT2.B7

@[expose] def n2V (x : Nat) : V2 := ⟨UInt64.ofNat (x % 2 ^ 64), UInt64.ofNat (x / 2 ^ 64)⟩

theorem v2N_n2V {x : Nat} (hx : x < 2 ^ 112) : v2N (n2V x) = x ∧ (n2V x).wf = true := by
  have h1 : x / 2 ^ 64 < 2 ^ 48 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc x < 2 ^ 112 := hx
      _ = 2 ^ 48 * 2 ^ 64 := by norm_num
  have hlo : (UInt64.ofNat (x % 2 ^ 64)).toNat = x % 2 ^ 64 := by
    rw [UInt64.toNat_ofNat', Nat.mod_mod]
  have hhi : (UInt64.ofNat (x / 2 ^ 64)).toNat = x / 2 ^ 64 := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 (by norm_num))
  refine ⟨?_, ?_⟩
  · unfold v2N n2V
    simp only
    rw [hlo, hhi]
    apply Nat.eq_of_testBit_eq
    intro i
    change (x % 2 ^ 64 ||| (x / 2 ^ 64) <<< 64).testBit i = x.testBit i
    rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_div_two_pow]
    by_cases hi : i < 64
    · simp [hi, show ¬ 64 ≤ i by omega]
    · simp [hi, show 64 ≤ i by omega, show i - 64 + 64 = i by omega]
  · unfold V2.wf n2V
    simp only [beq_iff_eq]
    apply UInt64.toNat_inj.1
    rw [UInt64.toNat_shiftRight, hhi]
    simp only [UInt64.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by simpa using h1)

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem vecLFrom_acc (x : Nat) : ∀ (rs : List Nat) (k acc : Nat),
    vecLFrom x rs k acc = acc ^^^ vecLFrom x rs k 0
  | [], _, acc => by
    change acc = acc ^^^ 0
    rw [Nat.xor_zero]
  | r :: rs, k, acc => by
    change Bool.rec (motive := fun _ => Nat) (vecLFrom x rs (Nat.succ k) acc)
        (CFSG.KC.Loop.strictN (Nat.xor acc r) (vecLFrom x rs (Nat.succ k)))
        (Nat.beq (Nat.land (Nat.shiftRight x k) 1) 1) =
      acc ^^^ Bool.rec (motive := fun _ => Nat) (vecLFrom x rs (Nat.succ k) 0)
        (CFSG.KC.Loop.strictN (Nat.xor 0 r) (vecLFrom x rs (Nat.succ k)))
        (Nat.beq (Nat.land (Nat.shiftRight x k) 1) 1)
    rw [strictN_eq', strictN_eq']
    cases Nat.beq (Nat.land (Nat.shiftRight x k) 1) 1
    · exact vecLFrom_acc x rs _ acc
    · change vecLFrom x rs (Nat.succ k) (Nat.xor acc r) =
        acc ^^^ vecLFrom x rs (Nat.succ k) (Nat.xor 0 r)
      rw [vecLFrom_acc x rs _ (Nat.xor acc r), vecLFrom_acc x rs _ (Nat.xor 0 r)]
      change (acc ^^^ r) ^^^ _ = acc ^^^ ((0 ^^^ r) ^^^ _)
      rw [Nat.zero_xor, Nat.xor_assoc]

@[expose] noncomputable def vtm (x M k : Nat) : Nat := Nat.mul (Nat.land (Nat.shiftRight x k) 1) (rowJ rm M k)

theorem vecLFrom_range (x M : Nat) : ∀ (n k : Nat),
    vecLFrom x ((List.range' k n).map (rowJ rm M)) k 0 =
      Nat.rec (motive := fun _ => Nat) 0 (fun i a => a ^^^ vtm x M (k + i)) n
  | 0, _ => rfl
  | n + 1, k => by
    have hR : ∀ n k, Nat.rec (motive := fun _ => Nat) 0 (fun i a => a ^^^ vtm x M (k + i)) (n + 1) =
        vtm x M k ^^^ Nat.rec (motive := fun _ => Nat) 0 (fun i a => a ^^^ vtm x M (k + 1 + i)) n := by
      intro n
      induction n with
      | zero => intro k; simp
      | succ n ih =>
        intro k
        change Nat.rec (motive := fun _ => Nat) 0 (fun i a => a ^^^ vtm x M (k + i)) (n + 1) ^^^
            vtm x M (k + (n + 1)) =
          vtm x M k ^^^ (Nat.rec (motive := fun _ => Nat) 0 (fun i a => a ^^^ vtm x M (k + 1 + i)) n ^^^
            vtm x M (k + 1 + n))
        rw [ih k, Nat.xor_assoc, show k + (n + 1) = k + 1 + n by omega]
    rw [hR, ← vecLFrom_range x M n (k + 1), List.range'_succ, List.map_cons]
    change Bool.rec (motive := fun _ => Nat) (vecLFrom x _ (Nat.succ k) 0)
        (CFSG.KC.Loop.strictN (Nat.xor 0 (rowJ rm M k)) (vecLFrom x _ (Nat.succ k)))
        (Nat.beq (Nat.land (Nat.shiftRight x k) 1) 1) = _
    rw [strictN_eq', vecLFrom_acc x _ _ (Nat.xor 0 (rowJ rm M k))]
    have hb : Nat.land (Nat.shiftRight x k) 1 = 0 ∨ Nat.land (Nat.shiftRight x k) 1 = 1 := by
      have : Nat.land (Nat.shiftRight x k) 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
      omega
    unfold vtm
    rcases hb with hb | hb
    · rw [hb]
      change vecLFrom x _ (Nat.succ k) 0 = 0 * rowJ rm M k ^^^ _
      rw [Nat.zero_mul, Nat.zero_xor]
    · rw [hb]
      change (0 ^^^ rowJ rm M k) ^^^ vecLFrom x _ (Nat.succ k) 0 = 1 * rowJ rm M k ^^^ _
      rw [Nat.zero_xor, Nat.one_mul]

theorem rowsOfJ_eq (M : Nat) : rowsOfJ rm M = (List.range' 0 112).map (rowJ rm M) := by
  have e : (Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun k ih acc => ih (List.cons k acc)) (nat_lit 112) List.nil) = List.range' 0 112 := by
    decide
  unfold rowsOfJ
  rw [e]

theorem vecLJ_rows (x M : Nat) : vecLJ x (rowsOfJ rm M) = vecJ rm x M := by
  rw [rowsOfJ_eq]
  unfold vecLJ vecJ
  rw [vecLFrom_range, strictN_eq', strictN_eq']
  simp only [Nat.zero_add]
  rfl

theorem b7Lit_parts (h : b7LitOK = true) :
    getN one B7V 0 = wordJ c rm one G5 G5i b7TW ∧
      (∀ i < 3, getN one B7V (i + 1) = mulJ c rm (mulJ c rm b7Xi (getN one B7V i)) b7XiI) ∧
      canonJ pad B7G0I = true ∧ Nat.beq (mulJ c rm (wordJ c rm one G5 G5i b7G0W) B7G0I) one = true ∧
      b7Xi = wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] [1, 2, -3, 1, 2, -3] ∧
      canonJ pad b7XiI = true ∧ Nat.beq (mulJ c rm b7Xi b7XiI) one = true := by
  unfold b7LitOK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, fun i hi => Nat.eq_of_beq_eq_true (allR_spec h2 i hi), h3, h4,
    Nat.eq_of_beq_eq_true h5, h6, h7⟩

theorem b7TWord_eq : CFSG.QuasithinUnique.A5.B7.b7TWord = b7TW := by
  unfold CFSG.QuasithinUnique.A5.B7.b7TWord b7TW
  rw [b7w_eq]
  rfl

theorem g0_enc : WfA (wR CFSG.QuasithinUnique.A5.B7.b7G0) ∧
    encR (wR CFSG.QuasithinUnique.A5.B7.b7G0) = wordJ c rm one G5 G5i b7G0W := wR_enc _

theorem vRows_get (T : Array V2) :
    (vRows T)[0]?.getD idRows = T ∧ (vRows T)[1]?.getD idRows = conjXi T ∧
      (vRows T)[2]?.getD idRows = conjXi (conjXi T) ∧
      (vRows T)[3]?.getD idRows = conjXi (conjXi (conjXi T)) := ⟨rfl, rfl, rfl, rfl⟩

theorem vRows_size' (T : Array V2) : (vRows T).size = 4 := rfl

section Lit

variable (hl : b7LitOK = true)
include hl

theorem five_enc' : WfA fiveRows ∧ encR fiveRows = b7Xi := by
  refine ⟨five_enc.1, five_enc.2.trans ?_⟩
  rw [(b7Lit_parts hl).2.2.2.2.1]
  rfl

theorem xiInv_enc : WfA xiInv ∧ encR xiInv = b7XiI := by
  have h := b7Lit_parts hl
  unfold xiInv
  exact invRows_enc hK (five_enc' hl).1 h.2.2.2.2.2.1 (by rw [(five_enc' hl).2]; exact h.2.2.2.2.2.2)

theorem conjXi_enc {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t) :
    WfA (conjXi T) ∧ encR (conjXi T) = mulJ c rm (mulJ c rm b7Xi t) b7XiI :=
  mul_enc hK (mul_enc hK (five_enc' hl) hT) (xiInv_enc hl)

theorem t0_enc : WfA (wR CFSG.QuasithinUnique.A5.B7.b7TWord) ∧
    encR (wR CFSG.QuasithinUnique.A5.B7.b7TWord) = getN one B7V 0 := by
  rw [b7TWord_eq]
  exact ⟨(wR_enc _).1, (wR_enc _).2.trans (b7Lit_parts hl).1.symm⟩

theorem vRows_enc {i : Nat} (hi : i < 4) :
    WfA ((vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord))[i]?.getD (idRows ())) ∧
      encR ((vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord))[i]?.getD (idRows ())) = getN one B7V i := by
  have h := (b7Lit_parts hl).2.1
  have e0 := t0_enc hl
  have e1 : WfA (conjXi (wR CFSG.QuasithinUnique.A5.B7.b7TWord)) ∧
      encR (conjXi (wR CFSG.QuasithinUnique.A5.B7.b7TWord)) = getN one B7V 1 := by
    have := conjXi_enc hl e0
    exact ⟨this.1, this.2.trans (h 0 (by decide)).symm⟩
  have e2 : WfA (conjXi (conjXi (wR CFSG.QuasithinUnique.A5.B7.b7TWord))) ∧
      encR (conjXi (conjXi (wR CFSG.QuasithinUnique.A5.B7.b7TWord))) = getN one B7V 2 := by
    have := conjXi_enc hl e1
    exact ⟨this.1, this.2.trans (h 1 (by decide)).symm⟩
  have e3 : WfA (conjXi (conjXi (conjXi (wR CFSG.QuasithinUnique.A5.B7.b7TWord)))) ∧
      encR (conjXi (conjXi (conjXi (wR CFSG.QuasithinUnique.A5.B7.b7TWord)))) = getN one B7V 3 := by
    have := conjXi_enc hl e2
    exact ⟨this.1, this.2.trans (h 2 (by decide)).symm⟩
  obtain ⟨g0, g1, g2, g3⟩ := vRows_get (wR CFSG.QuasithinUnique.A5.B7.b7TWord)
  interval_cases i
  · rw [g0]
    exact e0
  · rw [g1]
    exact e1
  · rw [g2]
    exact e2
  · rw [g3]
    exact e3

theorem g0i_enc : WfA (invRows (wR CFSG.QuasithinUnique.A5.B7.b7G0)) ∧
    encR (invRows (wR CFSG.QuasithinUnique.A5.B7.b7G0)) = B7G0I := by
  have h := b7Lit_parts hl
  exact invRows_enc hK (g0_enc).1 h.2.2.1 (by rw [g0_enc.2]; exact h.2.2.2.1)

theorem prod_enc (k : Nat) :
    WfA (prodRows (vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord)) k) ∧
      encR (prodRows (vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord)) k) = etaK c rm one B7V k := by
  have hlen : B7V.length = 4 := rfl
  have := enc_etaRows hK (T := vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord)) (Ts := B7V)
    (fun j hj => vRows_enc hl (by rw [hlen] at hj; exact hj)) k
  rw [hlen] at this
  exact this

end Lit

theorem getW_eq : ∀ (l : List (List Int)) (i : Nat), getW l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getW_eq l i

theorem vB7W_len : vB7W.length = 4 := rfl

theorem frApply_enc {M : Array V2} {m : Nat} (hM : WfA M ∧ encR M = m) {v : V2} (hv : v.wf = true) :
    (frApply (frTable M) v).wf = true ∧ v2N (frApply (frTable M) v) = vecJ rm (v2N v) m :=
  ⟨wf_frApply hM.1 v, by rw [v2N_frApply hK hM.1 hv, hM.2]⟩

theorem differs_beq {a b : V2} (ha : a.wf = true) (hb : b.wf = true) :
    (!(differs a b)) = Nat.beq (v2N a) (v2N b) := by
  rw [differs_eq ha hb, neN_eq, Bool.not_not]

theorem fixedBy_eq (hl : b7LitOK = true) {q : V2} (hq : q.wf = true) :
    fixedBy ((vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord)).map frTable) q =
      allR 4 fun i => Nat.beq (vecJ rm (v2N q) (getN one B7V i)) (v2N q) := by
  unfold fixedBy
  rw [allR_eq]
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  refine forall₂_congr fun i hi => ?_
  have hi' := List.mem_range.1 hi
  have hget : (((vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord)).map frTable)[i]?.getD #[]) =
      frTable ((vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord))[i]?.getD idRows) := by
    have hs : i < (vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord)).size := by
      rw [vRows_size']
      exact hi'
    rw [Array.getElem?_map, Array.getElem?_eq_getElem hs]
    simp
  rw [hget]
  have he := frApply_enc (vRows_enc hl hi') hq
  rw [differs_beq he.1 hq, he.2]

theorem neId_eq {M : Array V2} {m : Nat} (hM : WfA M ∧ encR M = m) :
    neId M = notB (Nat.beq m one) := by
  have he := eqRows_of hM (id_enc hK)
  rw [← he, notB_eq]
  unfold neId eqRows
  obtain ⟨hs, hw⟩ := hM.1
  have hid := wf_idRows
  obtain ⟨hs', hw'⟩ := hid
  rw [hs, hs']
  simp only [beq_self_eq_true, Bool.true_and]
  apply Bool.eq_iff_iff.2
  rw [Bool.not_eq_true', List.any_eq_true, List.all_eq_false]
  refine exists_congr fun i => and_congr_right fun hi => ?_
  have hi' := List.mem_range.1 hi
  have ha : (M[i]?.getD V2.zero).wf = true := by
    rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]
    exact Array.all_eq_true.1 hw i (by omega)
  have hb : ((idRows ())[i]?.getD V2.zero).wf = true := by
    rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]
    exact Array.all_eq_true.1 hw' i (by omega)
  have hd := differs_beq ha hb
  constructor
  · intro h1 h2
    rw [h1] at hd
    rw [V2.beq_iff] at h2
    rw [h2, Nat.beq_refl] at hd
    exact absurd hd (by decide)
  · intro h1
    by_contra h2
    rw [Bool.not_eq_true] at h2
    rw [h2, Bool.not_false] at hd
    exact h1 (V2.beq_iff.2 (v2N_inj (Nat.eq_of_beq_eq_true hd.symm)))

theorem uRows_enc {j : Nat} (hj : j < 11) :
    WfA (uRows[j]?.getD idRows) ∧ encR (uRows[j]?.getD idRows) = getN one Us j :=
  uTab_enc j hj

theorem etaTab_enc (hE : ∀ t < 32, etaCK t = true) {e : Nat} (he : e < 2048) :
    WfA etaTab[e]! ∧ encR etaTab[e]! = CFSG.KD.ETA.EF e := by
  rw [CFSG.QuasithinUnique.A5.B7.etaTab_get he]
  exact ef_enc hE he

theorem actTab_eq (hE : ∀ t < 32, etaCK t = true) {Mq : Array V2} {mq : Nat} (hq : WfA Mq ∧ encR Mq = mq) (t : List Nat) :
    actTabOK Mq Mq t = b7ActK mq t := by
  unfold actTabOK b7ActK
  rw [lenK_eq, andB_eq, allR_eq]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, List.all_eq_true]
  refine and_congr_right fun _ => forall₂_congr fun j hj => ?_
  have hj' := List.mem_range.1 hj
  rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, getN_zero_eq, decide_eq_true_eq]
  refine and_congr_right fun hlt => ?_
  rw [eqRows_of (mul_enc hK (mul_enc hK hq (uRows_enc hj')) hq) (etaTab_enc hE hlt)]

theorem countP_eq (t : List Nat) :
    (List.range 2048).countP (fun c => actT t c == c) = fixFrom t 2048 := by
  rw [fixN_gen, List.countP_eq_length_filter]

theorem cntRowsT_eq (hE : ∀ t < 32, etaCK t = true) {K Ki M : Array V2} {k ki m : Nat} (hk : WfA K ∧ encR K = k)
    (hki : WfA Ki ∧ encR Ki = ki) (hm : WfA M ∧ encR M = m) (t : List Nat)
    (h1 : Nat.beq (mulJ c rm k ki) one = true) (h2 : Nat.beq (mulJ c rm m m) one = true)
    (h3 : b7ActK (mulJ c rm (mulJ c rm ki m) k) t = true) :
    cntRowsT K Ki M M t = some (fixFrom t 2048) := by
  have e1 : eqRows (mulRows K Ki) idRows = true := by
    rw [eqRows_of (mul_enc hK hk hki) (id_enc hK)]
    exact h1
  have e2 : eqRows (mulRows M M) idRows = true := by
    rw [eqRows_of (mul_enc hK hm hm) (id_enc hK)]
    exact h2
  have e3 : actTabOK (mulRows (mulRows Ki M) K) (mulRows (mulRows Ki M) K) t = true := by
    rw [actTab_eq hE (mul_enc hK (mul_enc hK hki hm) hk)]
    exact h3
  unfold cntRowsT
  simp only [e1, e2, Bool.and_self, ite_true]
  rw [if_pos e3, countP_eq]

theorem cand_of (hl : b7LitOK = true) (hE : ∀ t < 32, etaCK t = true) {qv : V2} (hqv : qv.wf = true)
    {kw : List Int} {k : Nat} {t : List Nat} (h : b7CandK (v2N qv) kw k t = true) :
    candOKW (vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord)) qv ⟨kw, k, t⟩ = true := by
  unfold b7CandK at h
  rw [orB_eq'', Bool.or_eq_true] at h
  unfold candOKW
  rw [Bool.or_eq_true]
  rcases h with h | h
  · left
    have he := frApply_enc (five_enc' hl) hqv
    rw [differs_beq he.1 hqv, he.2]
    exact h
  · right
    beta_reduce at h
    simp only [andB_eq, Bool.and_eq_true] at h
    obtain ⟨hcan, hkk, hroot, hk1, hk16, hne, hmm, hact, hcnt⟩ := h
    have hK' := wR_enc kw
    have hKi : WfA (invRows (wR kw)) ∧ encR (invRows (wR kw)) = wordJ c rm one G5 G5i (negRev kw) :=
      invRows_enc hK hK'.1 hcan (by rw [hK'.2]; exact hkk)
    have hM := prod_enc hl k
    dsimp only
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨?_, Nat.le_of_ble_eq_true hk1⟩, lt_of_blt hk16⟩, ?_⟩, ?_⟩
    · have he := frApply_enc hKi rootV_wf'
      rw [differs_beq he.1 hqv, he.2]
      exact hroot
    · rw [neId_eq hM]
      exact hne
    · rw [cntRowsT_eq hE hK' hKi hM t hkk hmm hact]
      rw [notB_eq] at hcnt
      have hne' : fixFrom t 2048 ≠ 128 := fun e => by
        rw [e, Nat.beq_refl] at hcnt
        exact absurd hcnt (by decide)
      simpa using hne'

theorem cand_pt (hl : b7LitOK = true) {x : Nat} (hx : x < 2 ^ 112) :
    (frApply (frTable (invRows (wR CFSG.QuasithinUnique.A5.B7.b7G0))) (n2V x)).wf = true ∧
      v2N (frApply (frTable (invRows (wR CFSG.QuasithinUnique.A5.B7.b7G0))) (n2V x)) =
        vecJ rm x B7G0I := by
  have h := frApply_enc (g0i_enc hl) (v2N_n2V hx).2
  rw [(v2N_n2V hx).1] at h
  exact h

@[expose] def B7Hyps : Prop :=
  b7LitOK = true ∧ (∀ t < 32, etaCK t = true) ∧ ∀ j < 221, b7WitK j = true

theorem fx_len : FX5.length = 172 ∧ FX6.length = 48 := ⟨rfl, rfl⟩

theorem b7Pt_succ (i : Nat) : b7Pt (i + 1) = getN 0 (FX5 ++ FX6) i := rfl

theorem pt_of_fx5 {x : Nat} (hx : x ∈ FX5) : ∃ j < 221, b7Pt j = x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  refine ⟨i + 1, by rw [fx_len.1] at hi; omega, ?_⟩
  rw [b7Pt_succ, getN_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem pt_of_fx6 {x : Nat} (hx : x ∈ FX6) : ∃ j < 221, b7Pt j = x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  refine ⟨FX5.length + i + 1, by rw [fx_len.1]; rw [fx_len.2] at hi; omega, ?_⟩
  rw [b7Pt_succ, getN_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi, Option.getD_some]

theorem wit_cand (h : B7Hyps) {j : Nat} (hj : j < 221) {qv : V2} (hqv : qv.wf = true)
    (hq : v2N qv = vecJ rm (b7Pt j) B7G0I) :
    ∃ w : B7Wit, candOKW (vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord)) qv w = true := by
  have hw := h.2.2 j hj
  unfold b7WitK at hw
  rw [← hq] at hw
  exact ⟨_, cand_of h.1 h.2.1 hqv hw⟩

theorem survP_pt (h : B7Hyps) {x : Nat} (hx : x < 2 ^ 112) {FXL : List Nat}
    (hFX : ∀ y ∈ FXL, ∃ j < 221, b7Pt j = y)
    (hc : orB (notB (b7Fixed x)) (inLK x FXL) = true) :
    survP (wR CFSG.QuasithinUnique.A5.B7.b7TWord) CFSG.QuasithinUnique.A5.B7.b7G0 (n2V x) := by
  obtain ⟨hwf, hv⟩ := cand_pt h.1 hx
  rw [orB_eq'', Bool.or_eq_true, notB_eq, Bool.not_eq_true'] at hc
  rcases hc with hc | hc
  · left
    rw [fixedBy_eq h.1 hwf, hv]
    exact hc
  · right
    obtain ⟨j, hj, e⟩ := hFX x (inLK_mem' hc)
    exact wit_cand h hj hwf (by rw [hv, e])

theorem survRoot_of (h : B7Hyps) :
    survP (wR CFSG.QuasithinUnique.A5.B7.b7TWord) CFSG.QuasithinUnique.A5.B7.b7G0 rootV := by
  right
  have he := frApply_enc (g0i_enc h.1) rootV_wf'
  exact wit_cand h (j := 0) (by decide) he.1 he.2

theorem v2N_lt {v : V2} (hv : v.wf = true) : v2N v < 2 ^ 112 := by
  unfold V2.wf at hv
  rw [beq_iff_eq] at hv
  have hhi : v.hi.toNat < 2 ^ 48 := by
    have := congrArg UInt64.toNat hv
    rw [UInt64.toNat_shiftRight, UInt64.toNat_zero] at this
    simp only [UInt64.toNat_ofNat] at this
    rw [Nat.shiftRight_eq_div_pow] at this
    have h2 : v.hi.toNat / 2 ^ 48 = 0 := by simpa using this
    exact (Nat.div_eq_zero_iff_lt (by positivity)).1 h2
  have hlo : v.lo.toNat < 2 ^ 64 := v.lo.toNat_lt
  unfold v2N
  change v.lo.toNat ||| v.hi.toNat <<< 64 < 2 ^ 112
  apply Nat.or_lt_two_pow
  · exact Nat.lt_of_lt_of_le hlo (by norm_num)
  · rw [Nat.shiftLeft_eq]
    calc v.hi.toNat * 2 ^ 64 < 2 ^ 48 * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right hhi (by positivity)
      _ = 2 ^ 112 := by norm_num

theorem n2V_v2N {v : V2} (hv : v.wf = true) : n2V (v2N v) = v :=
  v2N_inj (v2N_n2V (v2N_lt hv)).1

theorem rm_lt : rm < 2 ^ 112 := by decide

theorem land_rm_lt (e : Nat) : Nat.land e rm < 2 ^ 112 := Nat.lt_of_le_of_lt Nat.and_le_right rm_lt

theorem locTabs_get' {g : Nat} (hg : g < 3) :
    locTabs[g]! = frTable ((locMats ())[g]?.getD idRows) := by
  rw [locTabs, getElem!_pos _ g (by rw [Array.size_map, locMats_size]; exact hg), Array.getElem_map,
    Array.getElem?_eq_getElem (by rw [locMats_size]; exact hg), Option.getD_some]

theorem nodup_of_sub {l₁ l₂ : List Nat} (h₁ : l₁.Nodup) (hs : ∀ x ∈ l₁, x ∈ l₂)
    (hl : l₁.length = l₂.length) : l₂.Nodup := by
  classical
  have hc : l₁.toFinset.card ≤ l₂.toFinset.card :=
    Finset.card_le_card fun x hx => List.mem_toFinset.2 (hs x (List.mem_toFinset.1 hx))
  rw [List.toFinset_card_of_nodup h₁, List.card_toFinset] at hc
  have hd := (List.dedup_sublist l₂).eq_of_length_le (by rw [← hl]; exact hc)
  rw [← hd]
  exact List.nodup_dedup l₂

theorem pch_flatten (r : Nat) (CH : List (List Nat)) :
    (pchK rm r CH).flatten = vptsK rm r CH.flatten := by
  unfold pchK vptsK
  rw [List.flatten_cons, List.map_flatten]
  rfl

theorem lrs_get {g : Nat} (hg : g < 3) :
    (List.map (rowsOfJ rm) [L0, L1, L2]).getD g [] = rowsOfJ rm (getN one [L0, L1, L2] g) := by
  interval_cases g <;> rfl

theorem survOrb_of (h : B7Hyps) {ℓ cap : Nat} {CH SPC : List (List Nat)} {P0 : List Nat}
    (hℓ : ℓ < 7) (hsize : sizeK cap CH SPC = true)
    (htree : ∀ i < CH.length, vtB rm (rep 1 128 1024) [L0, L1, L2] (vptsK rm (repK ℓ) CH.flatten)
      (CH.getD i []) (P0.getD i 0) (1 + 1024 * i) = true)
    (hsinc : sincK SPC.flatten 0 = true)
    (hsp : ∀ i < SPC.length, spInK (SPC.getD i []) (pchK rm (repK ℓ) CH) = true)
    {FXL : List Nat} (hFX : ∀ y ∈ FXL, ∃ j < 221, b7Pt j = y)
    (hfix : ∀ i < CH.length, allLK (fun e => (fun x => orB (notB (b7Fixed x)) (inLK x FXL))
      (Nat.land e rm)) (CH.getD i []) = true)
    (hroot : orB (notB (b7Fixed (repK ℓ))) (inLK (repK ℓ) FXL) = true) :
    survOrb (wR CFSG.QuasithinUnique.A5.B7.b7TWord) CFSG.QuasithinUnique.A5.B7.b7G0 ℓ cap := by
  obtain ⟨hpw, hpv⟩ := pathVec_enc (repPaths.getD ℓ [])
  have hr : v2N (pathVec (repPaths.getD ℓ [])) = repK ℓ := hpv
  simp only [sizeK, andB_eq, Bool.and_eq_true] at hsize
  obtain ⟨hs1, hs2, hs3, hs4, -⟩ := hsize
  have hlen : CH.flatten.length + 1 = cap := Nat.eq_of_beq_eq_true hs1
  have hSPl : SPC.flatten.length = cap := Nat.eq_of_beq_eq_true hs2
  set Pk := vptsK rm (repK ℓ) CH.flatten with hPk
  have hPkl : Pk.length = cap := by
    rw [hPk]
    unfold vptsK
    rw [List.length_cons, List.length_map, hlen]
  have hlt : ∀ y ∈ Pk, y < 2 ^ 112 := by
    intro y hy
    rw [hPk] at hy
    unfold vptsK at hy
    rcases List.mem_cons.1 hy with rfl | hy
    · rw [← hr]
      exact v2N_lt hpw
    · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
      exact land_rm_lt e
  have hget : ∀ k < Pk.length, Pk.getD k 0 < 2 ^ 112 := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]
    exact hlt _ (List.getElem_mem _)
  refine ⟨Pk.map n2V, ⟨?_, fun k hk0 hk => ?_⟩, ?_, by rw [List.length_map, hPkl], fun p hp => ?_⟩
  · rw [List.getElem?_map, hPk]
    unfold vptsK
    rw [List.getElem?_cons_zero, Option.map_some, ← hr, n2V_v2N hpw]
  · rw [List.length_map] at hk
    have hT := vtBs_sound (B := 1024) (consts_c hK).2 LRs_eq hlen
      (fun i hi => Nat.eq_of_beq_eq_true (allR_spec hs3 i (by omega)))
      (fun ch hch => Nat.le_of_ble_eq_true (List.all_eq_true.1 hs4 ch hch)) htree k hk0 (hPkl ▸ hk)
    obtain ⟨hpar, hlab, heq⟩ := hT
    set par := Nat.shiftRight (CH.flatten.getD (k - 1) 0) 114
    set lab := Nat.land (Nat.shiftRight (CH.flatten.getD (k - 1) 0) 112) 3
    have hlab3 : lab < 3 := hlab
    refine ⟨par, hpar, lab, hlab3, ?_⟩
    rw [getElem!_pos _ k (by rw [List.length_map]; exact hk),
      getElem!_pos _ par (by rw [List.length_map]; omega), List.getElem_map, List.getElem_map]
    have hpk : Pk.getD par 0 < 2 ^ 112 := hget par (by omega)
    have hfa := frApply_enc (loc_gens lab) (v2N_n2V hpk).2
    rw [(v2N_n2V hpk).1] at hfa
    rw [locTabs_get' hlab3, ← List.getD_eq_getElem _ 0 hk, ← List.getD_eq_getElem _ 0 (by omega)]
    apply v2N_inj
    rw [hfa.2, (v2N_n2V (hget k hk)).1, ← heq, LRs_eq, lrs_get hlab3, vecLJ_rows]
  · have hnd : Pk.Nodup := by
      refine nodup_of_sub (sincK_nodup hsinc) (fun x hx => ?_) (by rw [hSPl, hPkl])
      obtain ⟨sc, hsc, hxs⟩ := List.mem_flatten.1 hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hsc
      have := spInK_mem (hsp i hi) x (by rwa [List.getD_eq_getElem _ _ hi])
      obtain ⟨pc, hpc, hxp⟩ := this
      rw [hPk, ← pch_flatten]
      exact List.mem_flatten.2 ⟨pc, hpc, hxp⟩
    refine (List.nodup_map_iff_inj_on hnd).2 fun a ha b hb e => ?_
    rw [← (v2N_n2V (hlt a ha)).1, ← (v2N_n2V (hlt b hb)).1, e]
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hp
    refine ⟨(v2N_n2V (hlt y hy)).2, survP_pt h (hlt y hy) hFX ?_⟩
    rw [hPk] at hy
    unfold vptsK at hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hroot
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
      obtain ⟨ch, hch, hech⟩ := List.mem_flatten.1 he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hch
      have := mem_of_allLK (hfix i hi) (x := e) (by rwa [List.getD_eq_getElem _ _ hi])
      exact this

theorem baseP_of (h : B7Hyps) (hb : allR 15 (fun i => b7BaseK (Nat.succ i)) = true) :
    baseP (wR CFSG.QuasithinUnique.A5.B7.b7TWord) := by
  intro k hk1 hk16
  have hk := allR_spec hb (k - 1) (by omega)
  rw [show Nat.succ (k - 1) = k by omega] at hk
  unfold b7BaseK at hk
  beta_reduce at hk
  have hM := prod_enc h.1 k
  rw [orB_eq'', Bool.or_eq_true] at hk
  rcases hk with hk | hk
  · left
    rw [eqRows_of hM (id_enc hK)]
    exact hk
  · right
    simp only [andB_eq, Bool.and_eq_true] at hk
    obtain ⟨h1, h2, h3, h4⟩ := hk
    refine ⟨getL BT (Nat.sub k 1), ?_⟩
    rw [cntRowsT_eq h.2.1 (id_enc hK) (id_enc hK) hM _ h1 h2 h3, Nat.eq_of_beq_eq_true h4]

theorem chkB7V_of (h : B7Hyps) (hv : b7VK = true) :
    chkB7V (wR CFSG.QuasithinUnique.A5.B7.b7TWord) CFSG.QuasithinUnique.A5.B7.b7G0 387 = true := by
  have hl := h.1
  unfold b7VK at hv
  simp only [andB_eq, Bool.and_eq_true] at hv
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := hv
  unfold chkB7V
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, fun i hi => ?_⟩, fun i hi j hj => ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, by decide⟩, ?_⟩
  · rw [eqRows_of (mul_enc hK (five_enc' hl) (xiInv_enc hl)) (id_enc hK)]
    exact v1
  · rw [eqRows_of (mul_enc hK (vRows_enc hl hi) (vRows_enc hl hi)) (id_enc hK)]
    exact allR_spec v2 i hi
  · rw [eqRows_of (mul_enc hK (vRows_enc hl hi) (vRows_enc hl hj))
      (mul_enc hK (vRows_enc hl hj) (vRows_enc hl hi))]
    exact allR_spec (allR_spec v3 i hi) j hj
  · rw [eqRows_of (conjXi_enc hl (vRows_enc hl (i := 3) (by decide))) (prod_enc hl 15)]
    exact v4
  · have he := frApply_enc (vRows_enc hl (i := 0) (by decide)) rootV_wf'
    have hd := differs_beq he.1 rootV_wf'
    rw [he.2, v5] at hd
    simpa using hd
  · rw [eqRows_of (mul_enc hK g0_enc (g0i_enc hl)) (id_enc hK)]
    exact v6
  · rw [tMasks_eq, List.contains_iff_mem]
    exact inLK_mem' v7
  · rw [eqRows_of (mul_enc hK (mul_enc hK (g0i_enc hl) (vRows_enc hl (i := 0) (by decide))) g0_enc)
      (etaTab_enc h.2.1 (e := 387) (by decide))]
    exact v8

theorem rangeAny_eq (n : Nat) (f : Nat → Bool) :
    (List.range n).any f = notB (allR n fun k => notB (f k)) := by
  rw [allR_eq, notB_eq]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, Bool.not_eq_true', List.all_eq_false]
  simp [notB_eq]

theorem words_enc' {j : Nat} (hj : j < 4) :
    WfA (((CFSG.QuasithinUnique.A5.B7.b7ExplicitWords.map wR).toArray)[j]?.getD idRows) ∧
      encR (((CFSG.QuasithinUnique.A5.B7.b7ExplicitWords.map wR).toArray)[j]?.getD idRows) =
        getN one b7EK j := by
  rw [b7w_eq]
  have e : ((vB7W.map wR).toArray)[j]?.getD idRows = wR (getW vB7W j) := by
    have hl : j < vB7W.length := by rw [vB7W_len]; exact hj
    rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
      Option.getD_some, getW_eq, List.getD_eq_getElem _ _ hl]
  rw [e]
  refine ⟨(wR_enc _).1, (wR_enc _).2.trans ?_⟩
  unfold b7EK
  rw [smapK_eq, rangeK_eq, getN_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj]
  rfl

theorem cross_of (h : B7Hyps) (hc : b7CrossOK = true) :
    chkCross (vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord))
        (CFSG.QuasithinUnique.A5.B7.b7ExplicitWords.map wR).toArray = true ∧
      chkCross (CFSG.QuasithinUnique.A5.B7.b7ExplicitWords.map wR).toArray
        (vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord)) = true := by
  have hl := h.1
  unfold b7CrossOK at hc
  beta_reduce at hc
  rw [andB_eq, Bool.and_eq_true] at hc
  have hE4 : b7EK.length = 4 := by unfold b7EK; rw [smapK_eq, rangeK_eq]; simp
  have hV4 : B7V.length = 4 := rfl
  have etaW := fun k => enc_etaRows hK (T := (CFSG.QuasithinUnique.A5.B7.b7ExplicitWords.map wR).toArray)
    (Ts := b7EK) (fun j hj => words_enc' (by rw [hE4] at hj; exact hj)) k
  have etaV := fun k => enc_etaRows hK (T := vRows (wR CFSG.QuasithinUnique.A5.B7.b7TWord))
    (Ts := B7V) (fun j hj => vRows_enc hl (by rw [hV4] at hj; exact hj)) k
  rw [hE4] at etaW
  rw [hV4] at etaV
  unfold chkCross b7CrossK at *
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [rangeAny_eq]
    refine Eq.trans ?_ (allR_spec hc.1 j hj')
    apply congrArg notB
    rw [allR_eq, allR_eq]
    exact List.all_congr rfl fun k => by rw [eqRows_of (vRows_enc hl hj') (etaW k)]
  · rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [rangeAny_eq]
    refine Eq.trans ?_ (allR_spec hc.2 j hj')
    apply congrArg notB
    rw [allR_eq, allR_eq]
    exact List.all_congr rfl fun k => by rw [eqRows_of (words_enc' hj') (etaV k)]

end CertificateChecks.KernelJ4Q

end
