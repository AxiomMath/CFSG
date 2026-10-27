module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheckData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheckData
public import Certificates.Kernel.J4M2.C12633
public import Certificates.Kernel.J4M2.C4200
public import Certificates.Kernel.J4M2.ClosLo
public import Certificates.Kernel.J4M2.ClosHi
public import Certificates.Kernel.J4M2.NormLo
public import Certificates.Kernel.J4M2.NormHi
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4M2 CertificateChecks.KernelJ4Q CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck

theorem arr_eq {A B : Array V2} (hA : WfA A) (hB : WfA B) (h : encR A = encR B) : A = B :=
  CFSG.Sporadic.J4.eqRows_iff.1 (by rw [eqRows_eq hA hB, h]; exact Nat.beq_refl _)

theorem qaL_eq : qaL = QAs := rfl

theorem qiL_eq : qiL = QIs := rfl

@[expose] def stepQ (m : Nat) (acc : Array V2) (j : Nat) : Array V2 :=
  if m.testBit j then mulRows acc qM[j]! else acc

theorem qProd_false (m : Nat) : qProd m false = (List.range 12).foldl (stepQ m) (idRows ()) := by
  unfold qProd
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine foldl_congr_mem _ _ fun j hj acc => ?_
  have hj' := List.mem_range.1 hj
  unfold stepQ
  rw [qT_get hj', mulT_frTable]

theorem qProd_true (m : Nat) : qProd m true = mulRows (qProd m false) zM := by
  unfold qProd
  simp only [↓reduceIte, Bool.false_eq_true]
  rfl

theorem stepQ_wf {m : Nat} : ∀ (l : List Nat), (∀ j ∈ l, j < 12) → ∀ {A : Array V2}, WfA A →
    WfA (l.foldl (stepQ m) A)
  | [], _, _, h => h
  | j :: l, hl, A, h => by
    rw [List.foldl_cons]
    refine stepQ_wf l (fun i hi => hl i (List.mem_cons_of_mem _ hi)) ?_
    unfold stepQ
    split
    · exact wf_mulRows h (qM_enc (hl j List.mem_cons_self)).1
    · exact h

theorem stepQ_mul {m : Nat} : ∀ (l : List Nat), (∀ j ∈ l, j < 12) → ∀ {A : Array V2}, WfA A →
    l.foldl (stepQ m) A = mulRows A (l.foldl (stepQ m) (idRows ()))
  | [], _, _, h => (mulRows_idRows (rows_wf_of h)).symm
  | j :: l, hl, A, h => by
    have hl' : ∀ i ∈ l, i < 12 := fun i hi => hl i (List.mem_cons_of_mem _ hi)
    have hq := (qM_enc (hl j List.mem_cons_self)).1
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hb : m.testBit j
    · have e1 : ∀ B, stepQ m B j = mulRows B qM[j]! := fun B => by simp [stepQ, hb]
      rw [e1, e1, stepQ_mul l hl' (wf_mulRows h hq), stepQ_mul l hl' (wf_mulRows wf_idRows hq),
        idRows_mulRows hq, mulRows_assoc h hq (stepQ_wf l hl' wf_idRows)]
    · have e1 : ∀ B, stepQ m B j = B := fun B => by simp [stepQ, hb]
      rw [e1, e1]
      exact stepQ_mul l hl' h

theorem stepQ_congr {m m' : Nat} : ∀ (l : List Nat), (∀ j ∈ l, m.testBit j = m'.testBit j) →
    ∀ (A : Array V2), l.foldl (stepQ m) A = l.foldl (stepQ m') A
  | [], _, _ => rfl
  | j :: l, hl, A => by
    rw [List.foldl_cons, List.foldl_cons]
    have e1 : stepQ m A j = stepQ m' A j := by
      unfold stepQ
      rw [hl j List.mem_cons_self]
    rw [e1]
    exact stepQ_congr l (fun i hi => hl i (List.mem_cons_of_mem _ hi)) _

theorem stepQ_noop {m : Nat} : ∀ (l : List Nat), (∀ j ∈ l, m.testBit j = false) →
    ∀ (A : Array V2), l.foldl (stepQ m) A = A
  | [], _, _ => rfl
  | j :: l, hl, A => by
    rw [List.foldl_cons]
    have e1 : stepQ m A j = A := by
      unfold stepQ
      rw [hl j List.mem_cons_self]
      rfl
    rw [e1]
    exact stepQ_noop l (fun i hi => hl i (List.mem_cons_of_mem _ hi)) _

theorem testBit_lo (m j : Nat) : (m % 64).testBit j = (decide (j < 6) && m.testBit j) := by
  have e : (64 : Nat) = 2 ^ 6 := rfl
  rw [e, Nat.testBit_mod_two_pow]

theorem testBit_hi (m j : Nat) : (64 * (m / 64)).testBit j = (decide (6 ≤ j) && m.testBit j) := by
  have e : 64 * (m / 64) = (m >>> 6) <<< 6 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
  rw [e, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : 6 ≤ j
  · have e2 : 6 + (j - 6) = j := by omega
    simp [h, e2]
  · simp [h]

theorem range12 : List.range 12 = List.range 6 ++ List.range' 6 6 := by decide

theorem qProd_split (m : Nat) :
    qProd m false = mulRows (qProd (m % 64) false) (qProd (64 * (m / 64)) false) := by
  have h6 : ∀ j ∈ List.range 6, j < 12 := fun j hj => by have := List.mem_range.1 hj; omega
  have h66 : ∀ j ∈ List.range' 6 6, j < 12 := fun j hj => by
    have := List.mem_range'_1.1 hj; omega
  rw [qProd_false, qProd_false, qProd_false, range12, List.foldl_append, List.foldl_append,
    List.foldl_append]
  have hlo : (List.range 6).foldl (stepQ m) (idRows ()) = (List.range 6).foldl (stepQ (m % 64)) (idRows ()) :=
    stepQ_congr _ (fun j hj => by
      have := List.mem_range.1 hj
      rw [testBit_lo]
      simp [this]) _
  have hlo2 : ∀ A, (List.range' 6 6).foldl (stepQ (m % 64)) A = A := stepQ_noop _ fun j hj => by
    have := (List.mem_range'_1.1 hj).1
    rw [testBit_lo]
    have h' : ¬ j < 6 := by omega
    simp [h']
  have hhi1 : (List.range 6).foldl (stepQ (64 * (m / 64))) (idRows ()) = idRows () :=
    stepQ_noop _ (fun j hj => by
      have := List.mem_range.1 hj
      rw [testBit_hi]
      have h' : ¬ 6 ≤ j := by omega
      simp [h']) _
  have hhi2 : ∀ A, (List.range' 6 6).foldl (stepQ m) A = (List.range' 6 6).foldl (stepQ (64 * (m / 64))) A :=
    stepQ_congr _ fun j hj => by
      have := (List.mem_range'_1.1 hj).1
      rw [testBit_hi]
      have h' : 6 ≤ j := by omega
      simp [h']
  rw [hlo, hlo2, hhi1, hhi2]
  exact stepQ_mul _ h66 (stepQ_wf _ h6 wf_idRows)

theorem pK_enc (m : Nat) : WfA (qProd m false) ∧ encR (qProd m false) = pK m := by
  have h := qProd_enc m false
  rw [qProdK_eq] at h
  exact h

theorem getN_lo {k : Nat} (hk : k < 64) : getN one loL k = pK k := by
  rw [loL, smapK_eq, rangeK_eq, getN_map_range pK hk]

theorem getN_hi {k : Nat} (hk : k < 64) : getN one hiL k = pK (64 * k) := by
  rw [hiL, smapK_eq, rangeK_eq, getN_map_range (fun k => pK (64 * k)) hk]

theorem pT_eq {m : Nat} (hm : m < 4096) : pT loL hiL m = pK m := by
  unfold pT
  rw [getN_lo (Nat.mod_lt _ (by omega)), getN_hi (by omega), ← (pK_enc _).2, ← (pK_enc _).2,
    ← (pK_enc _).2, qProd_split m, enc_mulRows hK (pK_enc _).1 (pK_enc _).1]

@[expose] def iterA (i : Nat) (X : Array V2) : Array V2 := (List.range i).foldl (fun acc _ => mulT acc cTab) X

theorem iterA_succ (i : Nat) (X : Array V2) : iterA (i + 1) X = mulRows (iterA i X) cMat := by
  unfold iterA
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, cTab, mulT_frTable]

theorem wf_iterA {X : Array V2} (hX : WfA X) : ∀ i, WfA (iterA i X)
  | 0 => hX
  | i + 1 => by
    rw [iterA_succ]
    exact wf_mulRows (wf_iterA hX i) cMat_enc.1

theorem mul_iterA {G X : Array V2} (hG : WfA G) (hX : WfA X) :
    ∀ i, mulRows G (iterA i X) = iterA i (mulRows G X)
  | 0 => rfl
  | i + 1 => by
    rw [iterA_succ, iterA_succ, ← mul_iterA hG hX i, mulRows_assoc hG (wf_iterA hX i) cMat_enc.1]

theorem iterA_succ' {X : Array V2} (hX : WfA X) : ∀ i, iterA (i + 1) X = iterA i (mulRows X cMat)
  | 0 => by rw [iterA_succ]; rfl
  | i + 1 => by
    rw [iterA_succ, iterA_succ' hX i, iterA_succ]

theorem kRows_eq (f : Bool × Nat × Nat) : kRows f = iterA f.2.2 (qProd f.2.1 f.1) := rfl

theorem fact_chk : (Nat.beq (mulJ c rm ZM ZM) one && Nat.beq (mulJ c rm ZM cK) (mulJ c rm cK ZM) &&
    Nat.beq (mulJ c rm (mulJ c rm cK cK) cK) one) = true := by quickRfl

theorem zz_eq : mulRows zM zM = idRows () := by
  have h := fact_chk
  simp only [Bool.and_eq_true] at h
  exact arr_eq (wf_mulRows zM_enc.1 zM_enc.1) wf_idRows (by
    rw [enc_mulRows hK zM_enc.1 zM_enc.1, zM_enc.2, enc_idRows hK]
    exact Nat.eq_of_beq_eq_true h.1.1)

theorem zc_eq : mulRows zM cMat = mulRows cMat zM := by
  have h := fact_chk
  simp only [Bool.and_eq_true] at h
  exact arr_eq (wf_mulRows zM_enc.1 cMat_enc.1) (wf_mulRows cMat_enc.1 zM_enc.1) (by
    rw [enc_mulRows hK zM_enc.1 cMat_encK.1, enc_mulRows hK cMat_encK.1 zM_enc.1, zM_enc.2,
      cMat_encK.2]
    exact Nat.eq_of_beq_eq_true h.1.2)

theorem ccc_eq : mulRows (mulRows cMat cMat) cMat = idRows () := by
  have h := fact_chk
  simp only [Bool.and_eq_true] at h
  have w := cMat_encK
  exact arr_eq (wf_mulRows (wf_mulRows w.1 w.1) w.1) wf_idRows (by
    rw [(mul_enc hK (mul_enc hK w w) w).2, enc_idRows hK]
    exact Nat.eq_of_beq_eq_true h.2)

theorem iterA_three {X : Array V2} (hX : WfA X) : iterA 3 X = X := by
  have w := cMat_enc.1
  rw [iterA_succ, iterA_succ, iterA_succ]
  change mulRows (mulRows (mulRows X cMat) cMat) cMat = X
  rw [mulRows_assoc hX w w, mulRows_assoc hX (wf_mulRows w w) w, ccc_eq,
    mulRows_idRows (rows_wf_of hX)]

theorem z_cMat2 : mulRows zM (mulRows cMat cMat) = mulRows (mulRows cMat cMat) zM := by
  have w := cMat_enc.1
  have z := zM_enc.1
  rw [← mulRows_assoc z w w, zc_eq, mulRows_assoc w z w, zc_eq, ← mulRows_assoc w w z]

theorem wf_qProd (m : Nat) (e : Bool) : WfA (qProd m e) := (qProd_enc m e).1

theorem form_q {G : Array V2} (hG : WfA G) {m m' : Nat} {e' : Bool}
    (h : mulRows G (qProd m false) = qProd m' e') (e : Bool) :
    mulRows G (qProd m e) = qProd m' (xor e e') := by
  cases e
  · simpa using h
  · rw [qProd_true, ← mulRows_assoc hG (wf_qProd m false) zM_enc.1, h]
    cases e'
    · rw [← qProd_true]
      rfl
    · rw [qProd_true, mulRows_assoc (wf_qProd m' false) zM_enc.1 zM_enc.1, zz_eq,
        mulRows_idRows (rows_wf_of (wf_qProd m' false))]
      rfl

theorem form_c {G : Array V2} (hG : WfA G) (hz : mulRows zM G = mulRows G zM) {m m' : Nat} {e' : Bool}
    (h : mulRows G (qProd m false) = mulRows (qProd m' e') G) (e : Bool) :
    mulRows G (qProd m e) = mulRows (qProd m' (xor e e')) G := by
  cases e
  · simpa using h
  · have z := zM_enc.1
    rw [qProd_true, ← mulRows_assoc hG (wf_qProd m false) z, h,
      mulRows_assoc (wf_qProd m' e') hG z, ← hz, ← mulRows_assoc (wf_qProd m' e') z hG]
    have key : mulRows (qProd m' e') zM = qProd m' (xor true e') := by
      cases e'
      · rw [← qProd_true]
        rfl
      · rw [qProd_true, mulRows_assoc (wf_qProd m' false) z z, zz_eq,
          mulRows_idRows (rows_wf_of (wf_qProd m' false))]
        rfl
    rw [key]

theorem decodeF_codeF' (e : Bool) {c i : Nat} (hc : c < 4096) (hi : i < 3) :
    decodeF (codeF (e, c, i)) = (e, c, i) := by
  cases e <;> simp only [decodeF, codeF] <;> ext <;> simp <;> omega

theorem codeF_lt' (e : Bool) {c i : Nat} (hc : c < 4096) (hi : i < 3) : codeF (e, c, i) < 24576 := by
  cases e <;> simp only [codeF] <;> simp <;> omega

theorem hasForm_of {X : Array V2} {e : Bool} {m i : Nat} (h : X = kRows (e, m, i)) (hm : m < 4096)
    (hi : i < 3) : hasForm X m i = true := by
  unfold hasForm
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨decide_eq_true hm, decide_eq_true hi⟩, ?_⟩
  have hk : ∀ e', kTab[codeF (e', m, i)]! = kRows (e', m, i) := fun e' => by
    rw [kTab_get (codeF_lt' e' hm hi), decodeF_codeF' e' hm hi]
  rw [hk, hk, h]
  cases e <;> simp [CFSG.Sporadic.J4.eqRows_iff]

theorem twoK_spec {Y A B : Array V2} {y a b : Nat} (hY : WfA Y ∧ encR Y = y) (hA : WfA A ∧ encR A = a)
    (hB : WfA B ∧ encR B = b) (h : twoK y a b = true) : Y = A ∨ Y = B := by
  unfold twoK at h
  rw [orB_eq, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (arr_eq hY.1 hA.1 (by rw [hY.2, hA.2]; exact Nat.eq_of_beq_eq_true h))
  · exact Or.inr (arr_eq hY.1 hB.1 (by rw [hY.2, hB.2]; exact Nat.eq_of_beq_eq_true h))

theorem qProd_t_enc (m : Nat) : WfA (qProd m true) ∧ encR (qProd m true) = mulJ c rm (pK m) ZM := by
  have h := qProd_enc m true
  rw [qProdK_eq] at h
  exact h

theorem xor_lt {m j : Nat} (hm : m < 4096) (hj : j < 12) : m ^^^ 2 ^ j < 4096 :=
  Nat.xor_lt_two_pow (n := 12) hm (Nat.pow_lt_pow_right (by omega) hj)

theorem closM_spec {m : Nat} (hm : m < 4096) (h : closM loL hiL m = true) :
    (∀ j < 12, (∃ e', mulRows qM[j]! (qProd m false) = qProd (m ^^^ 2 ^ j) e') ∧
        (∃ e', mulRows qI[j]! (qProd m false) = qProd (m ^^^ 2 ^ j) e')) ∧
    cMask m < 4096 ∧ cMask (cMask m) < 4096 ∧
    (∃ e', mulRows cMat (qProd m false) = mulRows (qProd (cMask m) e') cMat) ∧
    (∃ e', mulRows (mulRows cMat cMat) (qProd m false) =
      mulRows (qProd (cMask (cMask m)) e') (mulRows cMat cMat)) := by
  have hP := pK_enc m
  have hC := cMat_encK
  have hC2 : WfA (mulRows cMat cMat) ∧ encR (mulRows cMat cMat) = cK2 := mul_enc hK hC hC
  have ex : ∀ {Y A B : Array V2} {y a b : Nat}, WfA Y ∧ encR Y = y → WfA A ∧ encR A = a →
      WfA B ∧ encR B = b → ∀ {F : Bool → Array V2}, F false = A → F true = B → twoK y a b = true →
      ∃ e', Y = F e' := fun hY hA hB F h0 h1 h => by
    rcases twoK_spec hY hA hB h with e | e
    · exact ⟨false, e.trans h0.symm⟩
    · exact ⟨true, e.trans h1.symm⟩
  unfold closM at h
  rw [strictB_eq, pT_eq hm, andB_eq, Bool.and_eq_true] at h
  obtain ⟨hq, hc⟩ := h
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨hb1, hb2⟩, hc⟩ := hc
  have hm1 := lt_of_blt hb1
  have hm2 := lt_of_blt hb2
  rw [strictB_eq, pT_eq hm1, andB_eq, Bool.and_eq_true, strictB_eq, pT_eq hm2] at hc
  refine ⟨fun j hj => ?_, hm1, hm2, ?_, ?_⟩
  · have h := allR_spec hq j hj
    rw [strictB_eq, pT_eq (xor_lt hm hj), strictB_eq, andB_eq, Bool.and_eq_true, qaL_eq, qiL_eq] at h
    exact ⟨ex (mul_enc hK (qM_enc hj) hP) (pK_enc _) (qProd_t_enc _) rfl rfl h.1,
      ex (mul_enc hK (qI_enc hj) hP) (pK_enc _) (qProd_t_enc _) rfl rfl h.2⟩
  · exact ex (mul_enc hK hC hP) (mul_enc hK (pK_enc _) hC) (mul_enc hK (qProd_t_enc _) hC)
      (F := fun e => mulRows (qProd (cMask m) e) cMat) rfl rfl hc.1
  · exact ex (mul_enc hK hC2 hP) (mul_enc hK (pK_enc _) hC2) (mul_enc hK (qProd_t_enc _) hC2)
      (F := fun e => mulRows (qProd (cMask (cMask m)) e) (mulRows cMat cMat)) rfl rfl hc.2

theorem clos_all {m : Nat} (hm : m < 4096) : closM loL hiL m = true := by
  have e : 128 * (m / 128) + m % 128 = m := Nat.div_add_mod m 128
  by_cases hlo : m / 128 < 16
  · have h := allR_spec (KCL.all (m / 128) hlo) (m % 128) (Nat.mod_lt _ (by omega))
    rwa [e] at h
  · have hlt : m / 128 - 16 < 16 := by omega
    have h0 := KCH.all (m / 128 - 16) hlt
    have e2 : closBlkHi (m / 128 - 16) = closBlk (m / 128) :=
      congrArg closBlk (Nat.add_sub_cancel' (by omega))
    have h : closBlk (m / 128) = true := e2 ▸ h0
    have h2 := allR_spec h (m % 128) (Nat.mod_lt _ (by omega))
    rwa [e] at h2

theorem decodeF_bounds {n : Nat} (hn : n < 24576) : (decodeF n).2.1 < 4096 ∧ (decodeF n).2.2 < 3 := by
  simp only [decodeF]
  omega

theorem cMat2_eq : cMat2 = mulRows cMat cMat := rfl

theorem closure_ok : chkClosure = true := by
  have hC := cMat_enc.1
  unfold chkClosure
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨by simp [kTab], ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < 24576 := by simpa [kTab] using hi
    have e := kTab_get hi'
    rw [getElem!_pos kTab i hi] at e
    rw [e]
    exact wf_bool (kRows_enc _).1
  rw [List.all_eq_true]
  intro n hn
  have hn' := List.mem_range.1 hn
  dsimp only
  rw [kTab_get hn']
  obtain ⟨hm, hi⟩ := decodeF_bounds hn'
  generalize decodeF n = f at hm hi ⊢
  obtain ⟨e, m, i⟩ := f
  simp only at hm hi ⊢
  obtain ⟨hq, -, -, ⟨e1, h1⟩, ⟨e2, h2⟩⟩ := closM_spec hm (clos_all hm)
  have hP := wf_qProd m e
  rw [kRows_eq]
  simp only
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun j hj => ?_, ?_⟩, ?_⟩
  · have hj' := List.mem_range.1 hj
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hq j hj'
    have hqj := (qM_enc hj').1
    have hij := (qI_enc hj').1
    rw [Bool.and_eq_true, mulT_frTable, mulT_frTable, mul_iterA hqj hP, mul_iterA hij hP,
      form_q hqj ha, form_q hij hb]
    exact ⟨hasForm_of rfl (xor_lt hm hj') hi, hasForm_of rfl (xor_lt hm hj') hi⟩
  · obtain ⟨-, hm1, -⟩ := closM_spec hm (clos_all hm)
    rw [mulT_frTable, mul_iterA hC hP, form_c hC zc_eq h1, ← iterA_succ' (wf_qProd _ _)]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hasForm_of rfl hm1 (by decide)
    · exact hasForm_of rfl hm1 (by decide)
    · rw [iterA_three (wf_qProd _ _)]
      exact hasForm_of rfl hm1 (by decide)
  · obtain ⟨-, -, hm2, -⟩ := closM_spec hm (clos_all hm)
    have hC2 := wf_mulRows hC hC
    rw [mulT_frTable, cMat2_eq, mul_iterA hC2 hP, form_c hC2 z_cMat2 h2,
      ← mulRows_assoc (wf_qProd _ _) hC hC, ← iterA_succ' (wf_mulRows (wf_qProd _ _) hC),
      ← iterA_succ' (wf_qProd _ _)]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hasForm_of rfl hm2 (by decide)
    · rw [iterA_three (wf_qProd _ _)]
      exact hasForm_of rfl hm2 (by decide)
    · rw [iterA_succ' (wf_qProd _ _), iterA_three (wf_mulRows (wf_qProd _ _) hC)]
      exact hasForm_of (i := 1) rfl hm2 (by decide)

theorem all_congr_mem {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.all f = l.all g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      all_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem any_congr_mem {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.any f = l.any g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self,
      any_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem k3F_bounds' : ∀ f ∈ k3F, f.2.1 < 4096 ∧ f.2.2 < 3 := by decide

theorem k3_enc {f : Bool × Nat × Nat} (hf : f ∈ k3F) :
    WfA kTab[codeF f]! ∧ encR kTab[codeF f]! = formK f := by
  obtain ⟨e, m, i⟩ := f
  obtain ⟨hm, hi⟩ := k3F_bounds' _ hf
  rw [kTab_get (codeF_lt' e hm hi), decodeF_codeF' e hm hi]
  exact kRows_enc _

theorem normK3_eq {M Mi : Array V2} {x xi : Nat} (hM : WfA M ∧ encR M = x)
    (hMi : WfA Mi ∧ encR Mi = xi) : normK3 M Mi = normK3K k3L x xi := by
  unfold normK3 normK3K k3Tabs k3L inK3 k3Mats
  dsimp only
  simp only [List.all_map, List.any_map, Function.comp_def]
  refine all_congr_mem fun f hf => ?_
  have hY := k3_enc hf
  rw [strictB_eq, mulT_frTable, mulT_frTable]
  refine any_congr_mem fun f' hf' => ?_
  rw [eqRows_of (mul_enc hK (mul_enc hK hM hY) hMi) (k3_enc hf')]

theorem norm_all {m : Nat} (hm : m < 4096) : normM loL hiL loiL hiiL m = true := by
  have e : 128 * (m / 128) + m % 128 = m := Nat.div_add_mod m 128
  by_cases hlo : m / 128 < 16
  · have h := allR_spec (KNL.all (m / 128) hlo) (m % 128) (Nat.mod_lt _ (by omega))
    rwa [e] at h
  · have hlt : m / 128 - 16 < 16 := by omega
    have h0 := KNH.all (m / 128 - 16) hlt
    have e2 : normBlkHi (m / 128 - 16) = normBlk (m / 128) :=
      congrArg normBlk (Nat.add_sub_cancel' (by omega))
    have h : normBlk (m / 128) = true := e2 ▸ h0
    have h2 := allR_spec h (m % 128) (Nat.mod_lt _ (by omega))
    rwa [e] at h2

theorem normOne_of {m : Nat} (hm : m < 4096) (e : Bool) {i : Nat} (hi : i < 3) :
    normOne (pK m) (piT loiL hiiL m) e m i = true := by
  have h := norm_all hm
  unfold normM at h
  rw [strictB_eq, strictB_eq, pT_eq hm] at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨a0, a1⟩, a2⟩, ⟨⟨b0, b1⟩, b2⟩⟩ := h
  cases e <;> rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> assumption

theorem norm_ok : chkNorm = true := by
  unfold chkNorm
  rw [List.all_eq_true]
  intro n hn
  have hn' := List.mem_range.1 hn
  dsimp only
  rw [kTab_get hn']
  obtain ⟨hm, hi⟩ := decodeF_bounds hn'
  generalize decodeF n = f at hm hi ⊢
  obtain ⟨e, m, i⟩ := f
  simp only at hm hi ⊢
  have hX := kRows_enc (e, m, i)
  have h := normOne_of hm e hi
  unfold normOne at h
  rw [strictB_eq, strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hcan, hmul⟩, hn3⟩ := h
  have hx : WfA (kRows (e, m, i)) ∧ encR (kRows (e, m, i)) =
      iterJ i (if e then mulJ c rm (pK m) ZM else pK m) := hX
  have hMi := invRows_enc hK hx.1 hcan (by rw [hx.2]; exact hmul)
  have hw : wfR (invRows (kRows (e, m, i))) = true := wf_bool hMi.1
  rw [hw, mulT_frTable, eqRows_of (mul_enc hK hx hMi) (id_enc hK), hmul, normK3_eq hx hMi]
  rw [orB_eq, notB_eq] at hn3
  simpa using hn3

@[expose] noncomputable def mK : Nat := [15, 29, 1, 7, 9, 11].foldl (fun acc n => mulJ c rm acc (gmK n)) one

@[expose] noncomputable def miK : Nat := [11, 9, 7, 1, 29, 15].foldl (fun acc n => mulJ c rm acc (giK n)) one

theorem m_chk : (canonJ pad miK && Nat.beq (mulJ c rm mK miK) one && normK3K k3L mK miK &&
    normK3K k3L miK mK) = true := by quickRfl

theorem mRows_enc : WfA mRows ∧ encR mRows = mK := by
  have key : ∀ (l : List Nat), (∀ n ∈ l, n < 32) → ∀ (acc : Array V2) (a : Nat), WfA acc ∧ encR acc = a →
      WfA (l.foldl (fun acc n => mulT acc gtabs[n]!) acc) ∧
        encR (l.foldl (fun acc n => mulT acc gtabs[n]!) acc) = l.foldl (fun acc n => mulJ c rm acc (gmK n)) a := by
    intro l
    induction l with
    | nil => intro _ acc a h; exact h
    | cons n l ih =>
      intro hl acc a h
      have hn := hl n List.mem_cons_self
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      rw [gtabs_get hn, mulT_frTable]
      exact mul_enc hK h (gm_enc hn)
  exact key _ (by decide) _ _ (id_enc hK)

theorem chkM_ok : chkM = true := by
  have h := m_chk
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hcan, hmul⟩, h1⟩, h2⟩ := h
  have hR := mRows_enc
  have hMi := invRows_enc hK hR.1 hcan (by rw [hR.2]; exact hmul)
  unfold chkM
  dsimp only
  have w1 : wfR mRows = true := wf_bool hR.1
  have w2 : wfR (invRows mRows) = true := wf_bool hMi.1
  rw [w1, w2, mulT_frTable, eqRows_of (mul_enc hK hR hMi) (id_enc hK), hmul, normK3_eq hR hMi, h1,
    normK3_eq hMi hR, h2]
  rfl

open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck in
theorem c12632 : kCheck = true := by
  unfold kCheck
  rw [closure_ok, norm_ok, chkM_ok]
  rfl

end CertificateChecks.KernelJ4M2

end
