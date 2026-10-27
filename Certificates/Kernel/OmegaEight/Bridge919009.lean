module

public import Certificates.Kernel.OmegaEight.C919009
public import Certificates.Kernel.OmegaEight.Bridge3002
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

set_option maxRecDepth 400000

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelO8.C919009

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEightMinus
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.CGT.Foote82.OmegaEight
  CFSG.CGT.Harada80 CertificateChecks.KernelO8

@[expose] def ofB (b : Bool) : ZMod 2 := if b then 1 else 0

theorem ofB_xor (a b : Bool) : ofB (a ^^ b) = ofB a + ofB b := by
  cases a <;> cases b <;> decide

theorem ofB_and (a b : Bool) : ofB (a && b) = ofB a * ofB b := by
  cases a <;> cases b <;> decide

theorem ofB_sq (a : Bool) : ofB a ^ 2 = ofB a := by
  cases a <;> decide

theorem ofB_false : ofB false = 0 := rfl

theorem ofB_true : ofB true = 1 := rfl

theorem vec_00 (x : ℕ) : vec 3 x (.inl 0) = ofB (x.testBit 0) := rfl
theorem vec_01 (x : ℕ) : vec 3 x (.inl 1) = ofB (x.testBit 1) := rfl
theorem vec_02 (x : ℕ) : vec 3 x (.inl 2) = ofB (x.testBit 2) := rfl
theorem vec_10 (x : ℕ) : vec 3 x (.inr (.inl 0)) = ofB (x.testBit 3) := rfl
theorem vec_11 (x : ℕ) : vec 3 x (.inr (.inl 1)) = ofB (x.testBit 4) := rfl
theorem vec_12 (x : ℕ) : vec 3 x (.inr (.inl 2)) = ofB (x.testBit 5) := rfl
theorem vec_20 (x : ℕ) : vec 3 x (.inr (.inr 0)) = ofB (x.testBit 6) := rfl
theorem vec_21 (x : ℕ) : vec 3 x (.inr (.inr 1)) = ofB (x.testBit 7) := rfl

theorem quad_expand (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) :
    CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 v =
      v (.inl 0) * v (.inr (.inl 0)) + v (.inl 1) * v (.inr (.inl 1)) +
        v (.inl 2) * v (.inr (.inl 2)) + v (.inr (.inr 0)) ^ 2 +
          1 * v (.inr (.inr 0)) * v (.inr (.inr 1)) + 1 * v (.inr (.inr 1)) ^ 2 := by
  simp only [CFSG.PGLModel.minusQuadForm, CFSG.MatrixModel.minusQuadCore, Fin.sum_univ_three]

theorem quad_vec (x : ℕ) :
    CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 x) = ofB (qNat x) := by
  rw [quad_expand]
  simp only [vec_00, vec_01, vec_02, vec_10, vec_11, vec_12, vec_20, vec_21, qNat, ofB_xor,
    ofB_and, ofB_sq, one_mul]
  ring

theorem polar_bNat (x u : ℕ) : polarCode 3 x u = ofB (bNat x u) := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  unfold polarCode
  rw [quad_expand, quad_expand, quad_expand]
  simp only [Pi.add_apply, vec_00, vec_01, vec_02, vec_10, vec_11, vec_12, vec_20, vec_21, bNat,
    ofB_xor, ofB_and, one_mul]
  linear_combination (ofB (x.testBit 6) * ofB (u.testBit 6) +
    ofB (x.testBit 7) * ofB (u.testBit 7)) * h2

theorem code_vec3 {c : ℕ} (hc : c < 256) : code (vec 3 c) = c := by
  have h256 : (2 : ℕ) ^ (3 + (3 + 2)) = 256 := rfl
  refine vec_inj (code_lt _) ?_ (vec_code _)
  rw [h256]
  exact hc

theorem reflCode_eq {u x : ℕ} (hu : u < 256) (hx : x < 256) : reflCode 3 u x = transNat u x := by
  unfold reflCode transNat
  rw [polar_bNat]
  cases bNat x u
  · rw [ofB_false, zero_smul, add_zero, if_neg Bool.false_ne_true]
    exact code_vec3 hx
  · rw [ofB_true, one_smul, ← vec_xor, if_pos rfl]
    exact code_vec3 (Nat.xor_lt_two_pow (n := 8) hx hu)

theorem quad_ne_zero (c : ℕ) :
    decide (CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0) = qNat c := by
  rw [quad_vec]
  cases qNat c <;> decide

theorem at8_lt (P i : ℕ) : at8 P i < 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem anyN_spec {n : ℕ} {f : ℕ → Bool} (h : CFSG.KLie.CT.anyN n f = true) :
    ∃ i < n, f i = true := by
  induction n with
  | zero => exact absurd h Bool.false_ne_true
  | succ n ih =>
    have e : CFSG.KLie.CT.anyN (n + 1) f = CFSG.KLie.CT.orB (f n) (CFSG.KLie.CT.anyN n f) := rfl
    rw [e] at h
    cases hf : f n
    · rw [hf] at h
      obtain ⟨i, hi, h'⟩ := ih h
      exact ⟨i, by omega, h'⟩
    · exact ⟨n, by omega, hf⟩

theorem b8K_lt2 (v w : ℕ) : b8K true v w < 2 := by
  have hbit : ∀ y j, bitN y j ≤ 1 := fun y j => Nat.and_le_right
  have hb : ∀ x y i j, bb x y i j < 2 := by
    intro x y i j
    have h1 : bb x y i j ≤ bitN y j := Nat.and_le_right
    exact Nat.lt_of_le_of_lt (Nat.le_trans h1 (hbit y j)) (by decide : (1 : ℕ) < 2)
  unfold b8K
  exact Nat.xor_lt_two_pow (n := 1) (Nat.xor_lt_two_pow (n := 1)
    (Nat.xor_lt_two_pow (n := 1) (hb _ _ _ _) (hb _ _ _ _))
    (Nat.xor_lt_two_pow (n := 1) (hb _ _ _ _) (hb _ _ _ _)))
    (Nat.xor_lt_two_pow (n := 1) (Nat.xor_lt_two_pow (n := 1) (hb _ _ _ _) (hb _ _ _ _))
      (Nat.xor_lt_two_pow (n := 1) (hb _ _ _ _) (hb _ _ _ _)))

theorem transNat_eqK {v x : ℕ} (hv : v < 256) (hx : x < 256) : transNat v x = transK true v x := by
  have hb := CertificateChecks.KernelO8.formM.2 x hx v hv
  have hl := b8K_lt2 x v
  unfold transNat transK
  rcases (by omega : b8K true x v = 0 ∨ b8K true x v = 1) with h | h
  · rw [h] at hb
    rw [hb, h, if_neg (by decide)]
    simp
  · rw [h] at hb
    rw [hb, h, if_pos (by decide)]
    simp

theorem transNat_lt {v x : ℕ} (hv : v < 256) (hx : x < 256) : transNat v x < 256 := by
  unfold transNat
  split
  · exact Nat.xor_lt_two_pow (n := 8) hx hv
  · exact hx

theorem transArr_eqK {c P : ℕ} (hc : c < 256) (h : transOK c P = true) :
    transArr c = unpack 136 8 P ∧ cnM P = true ∧
      allN 136 (fun i => Nat.blt (pg 8 (mask 8) P i) 136) = true := by
  unfold transOK at h
  simp only [bAnd_iff] at h
  obtain ⟨hcn, hrng, hall⟩ := h
  have hi : ∀ i < 136, at8 P i = at8 NIM (transK true c (at8 NSM i)) := fun i hi =>
    Nat.eq_of_beq_eq_true (allN_spec hall i hi)
  refine ⟨?_, hcn, hrng⟩
  have e : (fun i : Fin 136 => nsIdx[transNat c nsArr[i.val]!]!) =
      fun i : Fin 136 => pg 8 (mask 8) P i.val := by
    funext i
    have hns : nsArr[i.val]! = at8 NSM i.val := ns_bindM i.val i.2
    have hx : at8 NSM i.val < 256 := at8_lt NSM i.val
    have hy : transK true c (at8 NSM i.val) < 256 := by
      rw [← transNat_eqK hc hx]
      exact transNat_lt hc hx
    have hni : nsIdx[transK true c (at8 NSM i.val)]! = at8 NIM (transK true c (at8 NSM i.val)) :=
      ni_bindM _ hy
    have hP : (unpack 136 8 P)[i.val]! = at8 P i.val := at8_eq i.2
    have hP' : (unpack 136 8 P)[i.val]! = pg 8 (mask 8) P i.val := by
      unfold unpack
      exact CFSG.Monster.B.Co2.getElem!_ofFn_nat _ i.2
    rw [hns, transNat_eqK hc hx, hni, ← hP', hP, hi i.val i.2]
  unfold transArr unpack
  rw [e]

theorem allLK_spec {f : ℕ → Bool} : ∀ {cs : List ℕ}, allLK cs f = true → ∀ c ∈ cs, f c = true
  | [], _, c, hc => absurd hc List.not_mem_nil
  | a :: cs, h, c, hc => by
    have e : allLK (a :: cs) f = bAnd(f a, allLK cs f) := rfl
    rw [e, bAnd_iff] at h
    rcases List.mem_cons.1 hc with rfl | hc'
    · exact h.1
    · exact allLK_spec h.2 c hc'

theorem prodArr_eqK : ∀ cs : List ℕ, (∀ c ∈ cs, c < 256 ∧ transOK c (transCK c) = true) →
    prodArr cs = unpack 136 8 (prodK cs) ∧ cnM (prodK cs) = true
  | [], _ => ⟨by rw [prodArr, List.foldr_nil, idA_eqM]; rfl, kPidM'.1⟩
  | c :: cs, h => by
    obtain ⟨ih1, ih2⟩ := prodArr_eqK cs (fun d hd => h d (List.mem_cons_of_mem c hd))
    obtain ⟨hc1, hc2⟩ := h c List.mem_cons_self
    obtain ⟨ht, hcn, -⟩ := transArr_eqK hc1 hc2
    have e1 : prodArr (c :: cs) = compA 136 (transArr c) (prodArr cs) := List.foldr_cons
    have e2 : prodK (c :: cs) = pcM (transCK c) (prodK cs) := rfl
    rw [e1, ht, ih1, compA_pcM hcn ih2, e2]
    exact ⟨rfl, cn_pcM hcn ih2⟩

theorem cnAM {i : ℕ} (hi : i < 11) : cnM (AM.S i) = true := by
  have h := kStrCM
  simp only [bAnd_iff] at h
  exact allN_spec h.1 i hi

theorem qLink_k : qLinkCheck () = true := by
  unfold qLinkCheck
  rw [List.all_eq_true]
  intro c hc
  have hc' := List.mem_range.1 hc
  simp only [Bool.and_eq_true, quad_ne_zero, beq_self_eq_true, true_and, List.any_eq_true,
    List.mem_range]
  obtain ⟨j, hj, h⟩ := anyN_spec (allN_spec ch919009q c hc')
  refine ⟨j, hj, ?_⟩
  have e : nsArr[j]! = at8 NSM j := ns_bindM j hj
  rw [e, formM.1 _ (Nat.xor_lt_two_pow (n := 8) (at8_lt NSM j) hc'), beq_iff_eq]
  exact Nat.eq_of_beq_eq_true h

theorem reflLink_k : reflLinkCheck () = true := by
  unfold reflLinkCheck
  rw [List.all_eq_true]
  intro j hj
  rw [List.all_eq_true]
  intro x hx
  have hu : nsArr[j]! < 256 := by
    have e : nsArr[j]! = at8 NSM j := ns_bindM j (List.mem_range.1 hj)
    rw [e]
    exact at8_lt NSM j
  rw [reflCode_eq hu (List.mem_range.1 hx), beq_self_eq_true]

theorem transMem_k : transMemCheck () = true := by
  unfold transMemCheck autLevels
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  have h := allN_spec ch919009t j hj'
  simp only [bAnd_iff] at h
  have e : nsArr[j]! = at8 NSM j := ns_bindM j hj'
  rw [e]
  obtain ⟨ht, -, hr⟩ := transArr_eqK (at8_lt NSM j) h.1
  exact Orb.siftA_of_K bindsAQM (perm_of_head AQM.head) AQM.hl ht hr h.2

theorem eich_lists : ∀ i < 10, (decide ((eichRefl.getD i []).length % 2 = 0) &&
    (eichRefl.getD i []).all fun c => decide (c < 256) && qNat c) = true := by
  decide

theorem eich_k : eichCheck () = true := by
  have he := ch919009e
  simp only [bAnd_iff] at he
  obtain ⟨he1, he2, he3⟩ := he
  unfold eichCheck
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun i hi => ?_, ?_⟩
  · have hi' := List.mem_range.1 hi
    have h := allN_spec he1 i hi'
    simp only [bAnd_iff] at h
    have hcs : ∀ c ∈ eichRefl.getD i [], c < 256 ∧ transOK c (transCK c) = true := by
      intro c hc
      have := allLK_spec h.1 c hc
      simp only [bAnd_iff, Nat.blt_eq] at this
      exact ⟨this.1, this.2.2⟩
    obtain ⟨hp1, hp2⟩ := prodArr_eqK _ hcs
    rw [Bool.and_eq_true]
    refine ⟨eich_lists i hi', ?_⟩
    rw [genM_get (by omega), hp1, eqA_pcM (cnAM (by omega)) hp2]
    exact h.2
  · obtain ⟨ht, hcn, -⟩ := transArr_eqK (by decide) he2
    rw [genM_get (by decide), ht, eqA_pcM (cnAM (by decide)) hcn]
    exact he3

theorem bIf_ne {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem type_k : typeCheck () = true := by
  unfold typeCheck
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.1 hk
  have h := allN_spec ch919009w k hk'
  simp only [bAnd_iff] at h
  obtain ⟨hlet, hty⟩ := h
  have ht : witTypes.getD k 0 < 5 := by interval_cases k <;> decide
  obtain ⟨hy, hycn, -⟩ := main_okM ht
  unfold typeK typeZ at hty
  simp only [bAnd_iff] at hty
  obtain ⟨hgcn, hgpm, hgicn, hzcn, h12, h2cn, h3cn, h2, h3⟩ := hty
  have hcj := cn_cjM hgcn hgicn hycn
  dsimp only
  rw [hy, omegaW_eqM hlet, conjArr_cjM hgcn hgicn hgpm hycn, compA_pcM hycn hcj,
    powArr_pcM hzcn, powArr_pcM hzcn, powArr_pcM hzcn, idA_eqM, eqA_pcM h2cn kPidM'.1,
    eqA_pcM h3cn kPidM'.1, Nat.eq_of_beq_eq_true h12, eqA_pcM kPidM'.1 kPidM'.1, bIf_ne h2,
    bIf_ne h3, isInvA_ofM hgpm, Nat.beq_refl]
  rfl

theorem reflRep_k : reflRepCheck () = true := by
  unfold reflRepCheck
  have he := ch919009e
  simp only [bAnd_iff] at he
  obtain ⟨hm, hmcn, -⟩ := main_okM (i := 3) (by decide)
  obtain ⟨ht, hcn, -⟩ := transArr_eqK (by decide) he.2.1
  rw [hm, ht, eqA_pcM hmcn hcn]
  exact ch919009r

open Certificates in
open CFSG.CGT.Foote82.OmegaEight in
theorem cert919009 :
    (qLinkCheck () = true)
    ∧ (reflLinkCheck () = true)
    ∧ (transMemCheck () = true)
    ∧ (eichCheck () = true)
    ∧ (typeCheck () = true)
    ∧ (reflRepCheck () = true) :=
  ⟨qLink_k, reflLink_k, transMem_k, eich_k, type_k, reflRep_k⟩

end CertificateChecks.KernelO8.C919009
