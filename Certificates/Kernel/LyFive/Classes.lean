module

public import CFSG.Certificates.Kernel.LyFive.Orbit
public import Certificates.Kernel.LyFive.Checks
public import Certificates.Kernel.LyFive.CntA
public import Certificates.Kernel.LyFive.CntX
public import Certificates.Kernel.LyFive.CntY3
public import Certificates.Kernel.LyFive.CntY1
public import Certificates.Kernel.SporSch.Ly.Seven2189
import CFSG.Certificates.Kernel.SporSch.LyLoop
public import CFSG.Certificates.CosetTableShort
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.LySevenProof
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.OrbitSpec
public import Certificates.Certificate3085Base

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelLyFive

open CFSG.KS.LyFive.G2 CFSG.KS.LyFive.Bfs CFSG.KC.LyG2 CFSG.KC.Enum CertificateChecks.KernelLyFive.D
open CFSG.KS.SporSch.LyLoop CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open Matrix

theorem band {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  rw [bAnd_eqP, Bool.and_eq_true] at h
  exact h

theorem lvl_spec {ops : List (List ℕ)} {fixed : List ℕ} {b : ℕ} {ins : List (ℕ × ℕ × ℕ × List ℕ)}
    (h : lvlChk CC TT ops fixed b ins = true) :
    DataOK CC TT ops ∧ (∀ x ∈ fixed, Can x) ∧ Can b ∧ insOK ins = true ∧
      mRun (ccOf CC) (ops.map colM) (fixed.map dv ++ [dv b]) ins [] := by
  obtain ⟨h1, h⟩ := band h
  obtain ⟨h2, h⟩ := band h
  obtain ⟨h3, h⟩ := band h
  obtain ⟨h4, h5⟩ := band h
  have hD := dataOK_of data h3
  have hb : Can b := (redL_iff [b]).1 h2 b List.mem_cons_self
  have hF := (redL_iff fixed).1 h1
  refine ⟨hD, hF, hb, h4, ?_⟩
  have := (runI_iff hD (can_snoc hF hb) ins ((insOK_iff ins).1 h4) []
    (fun x hx => absurd hx List.not_mem_nil)).1 h5
  rw [snoc_eq, List.map_append, List.map_singleton, List.map_nil] at this
  exact this

theorem fin_spec {ops : List (List ℕ)} {fixed : List ℕ} {b : ℕ} {ins : List (ℕ × ℕ × ℕ × List ℕ)}
    {ui : List ℕ} (hl : lvlChk CC TT ops fixed b ins = true) (h : finChk CC ops fixed b ins ui = true) :
    colM ui * Matrix.of (fun r t : Fin 7 =>
      (mStk (ccOf CC) (ops.map colM) (fixed.map dv ++ [dv b]) ins []).getD t 0 r) = 1 := by
  obtain ⟨hD, hF, hb, -, -⟩ := lvl_spec hl
  obtain ⟨h1, h⟩ := band h
  obtain ⟨h2, h3⟩ := band h
  obtain ⟨hs, es⟩ := stkI_spec hD (can_snoc hF hb) ins [] (fun x hx => absurd hx List.not_mem_nil)
  have hinv := invChk_spec hs (by rw [← lenL_eq]; exact Nat.le_of_ble_eq_true h1)
    ((redL_iff ui).1 h2) h3
  rw [show (snoc fixed b).map dv = fixed.map dv ++ [dv b] by
    rw [snoc_eq, List.map_append, List.map_singleton], List.map_nil] at es
  rw [← es]
  convert hinv using 2
  ext r t
  simp only [colM, of_apply, dv_getL]

theorem nil_of_len {l : List ℕ} (h : Nat.beq (lenL l) 0 = true) : l = [] := by
  rw [Nat.beq_eq, lenL_eq] at h
  exact List.eq_nil_of_length_eq_zero h

theorem single_of_len {l : List ℕ} (h : Nat.beq (lenL l) 1 = true) : l = [getL l 0] := by
  rw [Nat.beq_eq, lenL_eq] at h
  match l, h with
  | [a], _ => rfl

theorem pair_of_len {l : List ℕ} (h : Nat.beq (lenL l) 2 = true) : l = [getL l 0, getL l 1] := by
  rw [Nat.beq_eq, lenL_eq] at h
  match l, h with
  | [a, b], _ => rfl

theorem cnt_sum {ops : List (List ℕ)} {fixed : List ℕ} {b : ℕ} {ins : List (ℕ × ℕ × ℕ × List ℕ)}
    {cnt : List ℕ} (hl : lvlChk CC TT ops fixed b ins = true)
    (hc : ∀ k < 25, cntChk CC TT ops fixed ins cnt k = true) :
    (passSet (ccOf CC) (ops.map colM) (fixed.map dv) ins).card = ∑ k ∈ Finset.range 25, getL cnt k := by
  obtain ⟨hD, hF, -, hins, -⟩ := lvl_spec hl
  rw [card_passSet_eq hD hF hins]
  exact Finset.sum_congr rfl fun k hk => Nat.eq_of_beq_eq_true (hc k (Finset.mem_range.1 hk))

theorem sum25 (cnt : List ℕ) : ∑ k ∈ Finset.range 25, getL cnt k =
    getL cnt 0 + getL cnt 1 + getL cnt 2 + getL cnt 3 + getL cnt 4 + getL cnt 5 + getL cnt 6 +
    getL cnt 7 + getL cnt 8 + getL cnt 9 + getL cnt 10 + getL cnt 11 + getL cnt 12 + getL cnt 13 +
    getL cnt 14 + getL cnt 15 + getL cnt 16 + getL cnt 17 + getL cnt 18 + getL cnt 19 + getL cnt 20 +
    getL cnt 21 + getL cnt 22 + getL cnt 23 + getL cnt 24 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]

theorem cntA0 : ∑ k ∈ Finset.range 25, getL a0_cnt k = 15624 := by rw [sum25]; decide
theorem cntA1 : ∑ k ∈ Finset.range 25, getL a1_cnt k = 3125 := by rw [sum25]; decide
theorem cntA2 : ∑ k ∈ Finset.range 25, getL a2_cnt k = 120 := by rw [sum25]; decide
theorem cntX0 : ∑ k ∈ Finset.range 25, getL x0_cnt k = 125 := by rw [sum25]; decide
theorem cntX1 : ∑ k ∈ Finset.range 25, getL x1_cnt k = 120 := by rw [sum25]; decide
theorem cntY3 : ∑ k ∈ Finset.range 25, getL y3_cnt k = 3750 := by rw [sum25]; decide
theorem cntY1 : ∑ k ∈ Finset.range 25, getL y1_cnt k = 1250 := by rw [sum25]; decide

theorem card_bot_of {K : Subgroup (M)ˣ} (h : ∀ g ∈ K, g = 1) : Nat.card K = 1 := by
  rw [(Subgroup.eq_bot_iff_forall K).2 h, Subgroup.card_bot]

theorem card_last {ops : List (List ℕ)} {fixed : List ℕ} {b : ℕ} {ins : List (ℕ × ℕ × ℕ × List ℕ)}
    {ui cnt : List ℕ} (hl : lvlChk CC TT ops fixed b ins = true) (hf : finChk CC ops fixed b ins ui = true)
    (hc : ∀ k < 25, cntChk CC TT ops fixed ins cnt k = true) :
    Nat.card (fixS (ccOf CC) (ops.map colM) (fixed.map dv)) ≤ ∑ k ∈ Finset.range 25, getL cnt k := by
  obtain ⟨-, -, -, -, hrun⟩ := lvl_spec hl
  have h := card_level_le (ccOf CC) (ops.map colM) hrun
  have h1 : Nat.card (fixS (ccOf CC) (ops.map colM) (fixed.map dv ++ [dv b])) = 1 := by
    refine card_bot_of fun g hg => ?_
    obtain ⟨hgA, hfix⟩ := (mem_fixS (ccOf CC) (ops.map colM)).1 hg
    exact eq_one_of_fix (ccOf CC) (ops.map colM) (fin_spec hl hf) hgA hfix
  rw [h1, Nat.mul_one, cnt_sum hl hc] at h
  exact h

theorem card_step {ops : List (List ℕ)} {fixed : List ℕ} {b : ℕ} {ins : List (ℕ × ℕ × ℕ × List ℕ)}
    {cnt : List ℕ} (hl : lvlChk CC TT ops fixed b ins = true)
    (hc : ∀ k < 25, cntChk CC TT ops fixed ins cnt k = true) :
    Nat.card (fixS (ccOf CC) (ops.map colM) (fixed.map dv)) ≤
      (∑ k ∈ Finset.range 25, getL cnt k) * Nat.card (fixS (ccOf CC) (ops.map colM) (fixed.map dv ++ [dv b])) := by
  obtain ⟨-, -, -, -, hrun⟩ := lvl_spec hl
  have h := card_level_le (ccOf CC) (ops.map colM) hrun
  rw [cnt_sum hl hc] at h
  exact h

theorem fixS_nil (ops : List M) : fixS (ccOf CC) ops [] = AC (ccOf CC) ops := by
  rw [fixS]
  exact CFSG.Sporadic.LySchreier.levelStab_zero _ _

theorem AC_nil : AC (ccOf CC) [] = A (ccOf CC) := by
  ext g
  exact ⟨fun h => h.1, fun h => ⟨h, fun o ho => absurd ho List.not_mem_nil⟩⟩

theorem card_A_le : Nat.card (A (ccOf CC)) ≤ 5859000000 := by
  have hfx := CertificateChecks.KernelLyFive.fixed
  have hcA := CertificateChecks.KernelLyFive.chainA
  simp only [bAnd_eqP, Bool.and_eq_true] at hfx hcA
  have hf0 := nil_of_len hfx.1
  have ha1 := single_of_len hcA.1
  have ha2 := pair_of_len hcA.2.2.1
  rw [Nat.eq_of_beq_eq_true hcA.2.1] at ha1
  rw [Nat.eq_of_beq_eq_true hcA.2.2.2.1, Nat.eq_of_beq_eq_true hcA.2.2.2.2] at ha2
  have s0 := card_step a0 A0.all
  have s1 := card_step a1 A1.all
  have s2 := card_last a2 a2f A2.all
  rw [hf0, cntA0] at s0
  rw [ha1, cntA1] at s1
  rw [ha2, cntA2] at s2
  simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append, List.singleton_append] at s0 s1 s2
  rw [← AC_nil, ← fixS_nil]
  calc Nat.card (fixS (ccOf CC) [] []) ≤ 15624 * Nat.card (fixS (ccOf CC) [] [dv a0_b]) := s0
    _ ≤ 15624 * (3125 * Nat.card (fixS (ccOf CC) [] [dv a0_b, dv a1_b])) := Nat.mul_le_mul_left _ s1
    _ ≤ 15624 * (3125 * 120) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ s2)
    _ = 5859000000 := by norm_num

theorem lt5L_iff (l : List ℕ) : lt5L l = true ↔ ∀ c ∈ l, c < 5 := by
  induction l with
  | nil => simp [lt5L]
  | cons c l ih =>
    change bAnd(Nat.blt c 5, lt5L l) = true ↔ _
    rw [bAnd_eqP, Bool.and_eq_true, Nat.blt_eq, ih, List.forall_mem_cons]

theorem tabOK : TabOK CC := (dataOK_of (ops := []) data rfl).tab

theorem hp_HP : hGenPairs asArr = CertificateChecks.KernelSporSch.LySv.HP := by
  unfold asArr
  rw [CertificateChecks.KernelSporSch.LyBSF.b4_eq]
  exact CertificateChecks.KernelSporSch.LySvF.hp_eq

theorem gM_isAut {j : ℕ} (hj : j < 5) : IsAut (ccOf CC) (gM j) := by
  have h := CFSG.KS.allN_spec gens j hj
  simp only [bAnd_eqP, Bool.and_eq_true] at h
  obtain ⟨h1, -, h3⟩ := h
  have hR := (lt5L_iff _).1 h1
  have e : gM j = colM (packCols (CertificateChecks.KernelSporSch.LySv.HP[j]!.1.toList)) := by
    rw [colM_packCols hR, gM, hp_HP]
  rw [e]
  exact isAut_of_autChk tabOK (packCols_ok hR).2 (packCols_ok hR).1 h3

theorem G7_le_A : G7 ≤ A (ccOf CC) := by
  rw [G7, Subgroup.closure_le]
  rintro u ⟨j, hj, e⟩
  change IsAut (ccOf CC) (u : M)
  rw [e]
  exact gM_isAut hj


theorem G7_eq_A : G7 = A (ccOf CC) :=
  Subgroup.eq_of_le_of_card_ge G7_le_A (card_A_le.trans card_G7_ge)

theorem card_G7 : Nat.card G7 = 5859000000 :=
  le_antisymm (G7_eq_A ▸ card_A_le) card_G7_ge

theorem cent_eq (X : M) : (G7 ⊓ CentS X : Subgroup (M)ˣ) = fixS (ccOf CC) [X] [] := by
  rw [fixS_nil, G7_eq_A]
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun o ho => by rw [List.mem_singleton.1 ho]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 X List.mem_cons_self⟩

theorem root_ok {R : List ℕ} (h1 : lt5L R = true) (h2 : Nat.beq (lenL R) 49 = true) :
    Red ⟨R⟩ ∧ colM (packCols R) = mat7 ⟨R⟩ := by
  have hR := (lt5L_iff R).1 h1
  refine ⟨⟨by rw [Nat.beq_eq, lenL_eq] at h2; simpa using h2, fun x hx => hR x (by simpa using hx)⟩,
    colM_packCols hR⟩

theorem rootsLt : lt5L RX = true ∧ lt5L RY3 = true ∧ lt5L RY1 = true := by
  have h := roots
  simp only [bAnd_eqP, Bool.and_eq_true] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem roots_ok : (Red ⟨RX⟩ ∧ colM (packCols RX) = mat7 ⟨RX⟩) ∧
    (Red ⟨RY3⟩ ∧ colM (packCols RY3) = mat7 ⟨RY3⟩) ∧ (Red ⟨RY1⟩ ∧ colM (packCols RY1) = mat7 ⟨RY1⟩) := by
  have h := roots
  simp only [bAnd_eqP, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨root_ok h1 h4, root_ok h2 h5, root_ok h3 h6⟩

theorem cls_ge {X : M} {N c : ℕ} (hc : Nat.card (fixS (ccOf CC) [X] []) ≤ c) (hNc : N * c = 5859000000) :
    N ≤ Nat.card (cls G7 X) := by
  have h := card_cls_mul G7 X
  rw [card_G7, cent_eq] at h
  by_contra hlt
  have : Nat.card (cls G7 X) * Nat.card (fixS (ccOf CC) [X] []) < N * c := by
    calc Nat.card (cls G7 X) * Nat.card (fixS (ccOf CC) [X] []) ≤ Nat.card (cls G7 X) * c :=
          Nat.mul_le_mul_left _ hc
      _ < N * c := Nat.mul_lt_mul_of_pos_right (by omega) (by
          rcases Nat.eq_zero_or_pos c with h0 | h0
          · rw [h0, Nat.mul_zero] at hNc; omega
          · exact h0)
  omega

theorem cls_x : 390600 ≤ Nat.card (cls G7 (mat7 ⟨RX⟩)) := by
  have hx := CertificateChecks.KernelLyFive.chainX
  simp only [bAnd_eqP, Bool.and_eq_true] at hx
  have hf1 := single_of_len hx.1
  rw [Nat.eq_of_beq_eq_true hx.2] at hf1
  have hfx := CertificateChecks.KernelLyFive.fixed
  simp only [bAnd_eqP, Bool.and_eq_true] at hfx
  have hf0 := nil_of_len hfx.2.1
  have s0 := card_step x0 X0.all
  have s1 := card_last x1 x1f X1.all
  rw [hf0, cntX0] at s0
  rw [hf1, cntX1] at s1
  simp only [List.map_nil, List.nil_append, List.map_cons] at s0 s1
  rw [roots_ok.1.2] at s0 s1
  refine cls_ge (c := 15000) ?_ (by norm_num)
  calc Nat.card (fixS (ccOf CC) [mat7 ⟨RX⟩] []) ≤ 125 * Nat.card (fixS (ccOf CC) [mat7 ⟨RX⟩] [dv x0_b]) := s0
    _ ≤ 125 * 120 := Nat.mul_le_mul_left _ s1
    _ = 15000 := by norm_num

theorem cls_y1 : 4687200 ≤ Nat.card (cls G7 (mat7 ⟨RY1⟩)) := by
  have hfx := CertificateChecks.KernelLyFive.fixed
  simp only [bAnd_eqP, Bool.and_eq_true] at hfx
  have hf0 := nil_of_len hfx.2.2.2
  have s := card_last y1 y1f Y1.all
  rw [hf0, cntY1] at s
  simp only [List.map_nil, List.map_cons] at s
  rw [roots_ok.2.2.2] at s
  exact cls_ge s (by norm_num)

theorem colM_mul_comm {R g : List ℕ} (hR : (packCols R).length ≤ 7 ∧ ∀ x ∈ packCols R, Can x)
    (hg : g.length ≤ 7 ∧ ∀ x ∈ g, Can x) (h : commChk (packCols R) g = true) :
    colM g * colM (packCols R) = colM (packCols R) * colM g := by
  ext r t
  have h1 := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h t.val t.isLt)
  have e1 := (mvL_spec hg.2 hg.1 (can_getL hR.2 t.val)).2
  have e2 := (mvL_spec hR.2 hR.1 (can_getL hg.2 t.val)).2
  rw [h1] at e1
  have key := congrFun (e1.symm.trans e2) r
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct] at key
  exact key

theorem card_cent_y3_ge : 3750 ≤ Nat.card (fixS (ccOf CC) [colM (packCols RY3)] []) := by
  have hlen : y3_wit.length = 3750 := (lenA_eq y3_wit).symm.trans (Nat.eq_of_beq_eq_true witsLen)
  have hok : ∀ i < 3750, witOK CC (packCols RY3) y3_wit[i]! = true := by
    intro i hi
    have h1 : i < y3_wit.length := by rw [hlen]; exact hi
    have h2 : i < 150 * 25 := Nat.lt_of_lt_of_le hi (Nat.le_of_eq rfl)
    exact blocks_all (nb := 25) (fun k hk => W3.all k hk) i h1 h2
  have hki := witsInc
  unfold keysInc at hki
  obtain ⟨-, hinc⟩ := keysInc_spec (b := y3_b) (l := y3_wit) 0 hki
  have hR := packCols_ok ((lt5L_iff RY3).1 rootsLt.2.1)
  have hparts : ∀ i < 3750, (y3_wit[i]!.1.length ≤ 7 ∧ ∀ x ∈ y3_wit[i]!.1, Can x) ∧
      (y3_wit[i]!.2.length ≤ 7 ∧ ∀ x ∈ y3_wit[i]!.2, Can x) ∧ invChk y3_wit[i]!.1 y3_wit[i]!.2 = true ∧
      autChk CC y3_wit[i]!.1 = true ∧ commChk (packCols RY3) y3_wit[i]!.1 = true := by
    intro i hi
    have h := hok i hi
    unfold witOK at h
    simp only [bAnd_eqP, Bool.and_eq_true] at h
    obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
    exact ⟨(matOK_iff _).1 h1, (matOK_iff _).1 h2, h3, h4, h5⟩
  have hunit : ∀ i < 3750, colM y3_wit[i]!.2 * colM y3_wit[i]!.1 = 1 := fun i hi =>
    invChk_spec (hparts i hi).1.2 (hparts i hi).1.1 (hparts i hi).2.1.2 (hparts i hi).2.2.1
  let u : Fin 3750 → (M)ˣ := fun i => ⟨colM y3_wit[i.val]!.1, colM y3_wit[i.val]!.2,
    mul_eq_one_comm.1 (hunit i.val i.isLt), hunit i.val i.isLt⟩
  have hmem : ∀ i, u i ∈ fixS (ccOf CC) [colM (packCols RY3)] [] := by
    intro i
    rw [fixS_nil]
    obtain ⟨hg, -, -, h4, h5⟩ := hparts i.val i.isLt
    refine ⟨isAut_of_autChk tabOK hg.2 hg.1 h4, fun o ho => ?_⟩
    rw [List.mem_singleton.1 ho]
    exact colM_mul_comm hR hg h5
  let φ : Fin 3750 → fixS (ccOf CC) [colM (packCols RY3)] [] := fun i => ⟨u i, hmem i⟩
  have hφ : Function.Injective φ := by
    intro i j e
    have e1 : colM y3_wit[i.val]!.1 = colM y3_wit[j.val]!.1 :=
      congrArg (fun x : fixS (ccOf CC) [colM (packCols RY3)] [] => ((x : (M)ˣ) : M)) e
    have hb : Can y3_b := (lvl_spec y3).2.2.1
    have ki := mvL_spec (hparts i.val i.isLt).1.2 (hparts i.val i.isLt).1.1 hb
    have kj := mvL_spec (hparts j.val j.isLt).1.2 (hparts j.val j.isLt).1.1 hb
    have ek : mvL y3_wit[i.val]!.1 y3_b = mvL y3_wit[j.val]!.1 y3_b :=
      can_eq ki.1 kj.1 (by rw [ki.2, kj.2, e1])
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact absurd ek (hinc i.val (by omega) j.val (by omega) h).ne
    · exact h
    · exact absurd ek (hinc j.val (by omega) i.val (by omega) h).ne'
  have := Nat.card_le_card_of_injective φ hφ
  simpa using this

theorem cls_y3 : Nat.card (cls G7 (mat7 ⟨RY3⟩)) = 1562400 := by
  have hfx := CertificateChecks.KernelLyFive.fixed
  simp only [bAnd_eqP, Bool.and_eq_true] at hfx
  have hf0 := nil_of_len hfx.2.2.1
  have s := card_last y3 y3f Y3.all
  rw [hf0, cntY3] at s
  simp only [List.map_nil, List.map_cons] at s
  have hlo := card_cent_y3_ge
  rw [roots_ok.2.1.2] at s hlo
  have h := card_cls_mul G7 (mat7 ⟨RY3⟩)
  rw [card_G7, cent_eq, le_antisymm s hlo] at h
  exact Nat.eq_of_mul_eq_mul_right (show 0 < 3750 by norm_num)
    (h.trans (show (5859000000 : ℕ) = 1562400 * 3750 by norm_num))

end CertificateChecks.KernelLyFive

end
