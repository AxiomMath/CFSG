module

public import CFSG.LargeExtraspecial.S63CD4InputsA
public import Certificates.Kernel.S63K.AChecks
public import CFSG.Certificates.Kernel.S63K.EnumSound
public import CFSG.Certificates.Kernel.S63K.PickSound
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.A21112

open CFSG.LargeExtraspecial.S63 CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KS.SporSch.M24 CFSG.KC.Enum
  CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2.Native
  CertificateChecks.KernelS63.AD

noncomputable abbrev DQ : EnumData := DkG QP QPar QLab 512

noncomputable abbrev DL : EnumData := DkG LP LPar LLab 504

theorem qg_size : qGens.size = 8 := by decide +kernel

theorem lg_size : lGens.size = 6 := by decide +kernel

theorem qg_chk : ((List.range 8).all fun l => qGens[l]! == unpackR 24 (QG l)) = true := by
  decide +kernel

theorem lg_chk : ((List.range 6).all fun l => lGens[l]! == unpackR 24 (LG l)) = true := by
  decide +kernel

theorem qg_eq : ∀ l < 8, qGens[l]! = unpackR 24 (QG l) := fun l hl => by
  have h := List.all_eq_true.1 qg_chk l (List.mem_range.2 hl)
  simpa using h

theorem lg_eq : ∀ l < 6, lGens[l]! = unpackR 24 (LG l) := fun l hl => by
  have h := List.all_eq_true.1 lg_chk l (List.mem_range.2 hl)
  simpa using h

theorem z_eq : z0R = unpackR 24 Zp := by decide +kernel

theorem dq_eq : mkEnum qGens = DQ := mkEnum_of_K qg_size qg_eq repQ

theorem dl_eq : mkEnum lGens = DL := mkEnum_of_K lg_size lg_eq repL

theorem q_el {i : ℕ} (hi : i < 512) : DQ.El[i]! = unpackR 24 (QP i) := elG_get hi

theorem l_el {i : ℕ} (hi : i < 504) : DL.El[i]! = unpackR 24 (LP i) := elG_get hi

theorem q_inv {i : ℕ} (hi : i < 512) : DQ.inv[i]! = QInv i ∧ QInv i < 512 :=
  ⟨(inv_of_K qg_size qg_eq repQ invQ hi).1, (inv_of_K qg_size qg_eq repQ invQ hi).2.1⟩

theorem l_inv {i : ℕ} (hi : i < 504) : DL.inv[i]! = LInv i ∧ LInv i < 504 :=
  ⟨(inv_of_K lg_size lg_eq repL invL hi).1, (inv_of_K lg_size lg_eq repL invL hi).2.1⟩

theorem memQ_eq (Y : ℕ) : memR DQ.El DQ.idx (unpackR 24 Y) = memQ Y :=
  memR_eq qg_size qg_eq repQ Y

theorem beqM (A B : ℕ) : (unpackR 24 A == unpackR 24 B) = eqM A B := beq_unpackR A B

theorem any_congr {p q : ℕ → Bool} : ∀ {l : List ℕ}, (∀ x ∈ l, p x = q x) → l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      any_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem subProds_map : ∀ L : List ℕ, subProds (L.map (unpackR 24)) = (subProdsK L).map (unpackR 24)
  | [] => by
    change [oneR] = [unpackR 24 idP]
    rw [oneR_eq]
  | y :: ys => by
    change subProds (unpackR 24 y :: ys.map (unpackR 24)) = _
    rw [subProds, subProds_map ys, subProdsK, List.map_append, List.map_map, List.map_map]
    refine congrArg (fun t => List.map (unpackR 24) (subProdsK ys) ++ t) ?_
    apply List.map_congr_left
    intro e _
    exact mulR_unpackR _ _

theorem powRows_unpackR (X : ℕ) : ∀ e, powRows 24 (unpackR 24 X) e = unpackR 24 (powK X e)
  | 0 => oneR_eq
  | e + 1 => by
    rw [powRows, powRows_unpackR X e]
    exact mulR_unpackR _ _

theorem testBit_maskOf : ∀ (rs : List ℕ) (acc j : ℕ),
    (rs.foldl (fun m r => Nat.lor m (Nat.shiftLeft 1 r)) acc).testBit j =
      (acc.testBit j || rs.contains j)
  | [], acc, j => by simp
  | r :: rs, acc, j => by
    have e : Nat.lor acc (Nat.shiftLeft 1 r) = acc ||| (1 <<< r) := rfl
    rw [List.foldl_cons, testBit_maskOf rs _ j, e, Nat.testBit_or, Nat.one_shiftLeft,
      Nat.testBit_two_pow, List.contains_cons]
    by_cases h : r = j
    · subst h
      simp
    · have h' : (j == r) = false := by simpa using Ne.symm h
      simp [h, h']

theorem marks_get (idx : Array ℕ → ℕ) {w : ℕ} :
    ∀ (ps : List (Array ℕ)) (a : Array Bool), w < a.size →
      ((∃ p ∈ ps, idx p = w) ∨ a[w]! = true) →
        (ps.foldl (fun m p => m.set! (idx p) true) a)[w]! = true
  | [], a, _, h => by
    rcases h with ⟨p, hp, _⟩ | h
    · exact absurd hp List.not_mem_nil
    · exact h
  | p :: ps, a, hw, h => by
    rw [List.foldl_cons]
    have hs : (a.set! (idx p) true).size = a.size := by simp
    apply marks_get idx ps _ (by rw [hs]; exact hw)
    rcases h with ⟨q, hq, he⟩ | h
    · rcases List.mem_cons.1 hq with rfl | hq
      · right
        rw [getElem!_pos _ w (by rw [hs]; exact hw)]
        simp [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds, he]
      · exact Or.inl ⟨q, hq, he⟩
    · right
      rw [getElem!_pos _ w (by rw [hs]; exact hw)]
      rw [getElem!_pos _ w hw] at h
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds hw]
      split <;> simp_all

theorem cover_of {ps : List ℕ} {R : ℕ} (h : covK ps R = true) :
    coverOK DQ.El DQ.idx (ps.map (unpackR 24)) = true := by
  unfold covK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨hl, hz⟩, hm⟩ := h
  have hpl : (posL R).length = 512 := by simp [posL]
  have hzip : ∀ s < 512, (posL R)[s]! < 512 ∧ eqM (QP (posL R)[s]!) ps[s]! = true := by
    intro s hs
    have hmem : (ps[s]!, (posL R)[s]!) ∈ ps.zip (posL R) := by
      rw [List.mem_iff_getElem]
      refine ⟨s, by simp [hl, hpl, hs], ?_⟩
      simp [getElem!_pos, hl, hpl, hs]
    have := hz _ hmem
    simpa [Bool.and_eq_true, Nat.blt_eq] using this
  have hsz : DQ.El.size = 512 := by simp [DkG, ElG]
  have hpos : ∀ s < 512, DQ.idx (unpackR 24 ps[s]!) = (posL R)[s]! := by
    intro s hs
    obtain ⟨h1, h2⟩ := hzip s hs
    rw [← eqM_iff.1 h2]
    exact idx_of_K qg_size qg_eq repQ h1
  unfold coverOK
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.1 hp
    rw [memQ_eq]
    have hs' : s < 512 := by omega
    obtain ⟨h1, h2⟩ := hzip s hs'
    rw [← getElem!_pos ps s hs]
    exact List.any_eq_true.2 ⟨_, List.mem_range.2 h1, h2⟩
  · rw [hsz]
    refine allLt_iff.2 fun j hj => ?_
    have hbit : (maskOf (posL R)).testBit j = true := by
      rw [hm, Nat.testBit_two_pow_sub_one]
      simpa using hj
    unfold maskOf at hbit
    rw [testBit_maskOf, Nat.zero_testBit, Bool.false_or, List.contains_iff_mem] at hbit
    obtain ⟨s, hs, hsj⟩ := List.mem_iff_getElem.1 hbit
    rw [hpl] at hs
    unfold marks
    apply marks_get _ _ _ (by simpa using hj)
    left
    refine ⟨unpackR 24 ps[s]!, List.mem_map.2 ⟨ps[s]!, ?_, rfl⟩, ?_⟩
    · rw [getElem!_pos ps s (by omega)]
      exact List.getElem_mem _
    · rw [hpos s hs, getElem!_pos _ s (by rw [hpl]; exact hs), hsj]

theorem gens_q : gensOK qGens = true := by
  unfold gensOK
  rw [qg_size]
  refine allLt_iff.2 fun k hk => ?_
  have h := MatL.allN_iff.1 gq k hk
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  rw [qg_eq k hk, mulR_unpackR, oneR_eq, beqM]
  exact h.1

theorem gens_l : gensOK lGens = true := by
  unfold gensOK
  rw [lg_size]
  refine allLt_iff.2 fun k hk => ?_
  have h := MatL.allN_iff.1 gl k hk
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  rw [lg_eq k hk, mulR_unpackR, oneR_eq, beqM]
  exact h.1

theorem comm_q : (allLt qGens.size fun k => mulR qGens[k]! z0R == mulR z0R qGens[k]!) = true := by
  rw [qg_size]
  refine allLt_iff.2 fun k hk => ?_
  have h := MatL.allN_iff.1 gq k hk
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  rw [qg_eq k hk, z_eq, mulR_unpackR, mulR_unpackR, beqM]
  exact h.2

theorem comm_l : (allLt lGens.size fun k => mulR lGens[k]! z0R == mulR z0R lGens[k]!) = true := by
  rw [lg_size]
  refine allLt_iff.2 fun k hk => ?_
  have h := MatL.allN_iff.1 gl k hk
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  rw [lg_eq k hk, z_eq, mulR_unpackR, mulR_unpackR, beqM]
  exact h.2

theorem mem_z : memR DQ.El DQ.idx z0R = true := by
  rw [z_eq, memQ_eq]
  exact zq

theorem a10 : (allLt 504 fun i => DL.El[i]! == oneR || !memR DQ.El DQ.idx DL.El[i]!) = true := by
  refine allLt_iff.2 fun i hi => ?_
  rw [l_el hi, oneR_eq, beqM, memQ_eq]
  exact MatL.allN_iff.1 t10 i hi

theorem a11 : (allLt lGens.size fun k => allLt 512 fun i =>
    memR DQ.El DQ.idx (conjR lGens[k]! DQ.El[i]!)) = true := by
  rw [lg_size]
  refine allLt_iff.2 fun k hk => allLt_iff.2 fun i hi => ?_
  rw [q_el hi, lg_eq k hk, conjR, mulR_unpackR, mulR_unpackR, memQ_eq]
  exact MatL.allN_iff.1 (MatL.allN_iff.1 t11 k hk) i hi

theorem a12 : (allLt 504 fun i => !(mulR DL.El[i]! DL.El[i]! == oneR) || DL.El[i]! == oneR ||
    (List.range 504).any fun c =>
      let m := mulR DL.El[i]! (conjI DL.El[c]! DL.El[DL.inv[c]!]! DL.El[i]!)
      !(m == oneR) && powRows 24 m 63 == oneR) = true := by
  refine allLt_iff.2 fun i hi => ?_
  have h := MatL.allN_iff.1 t12 i hi
  rw [l_el hi, mulR_unpackR, oneR_eq, beqM, beqM]
  rw [any_congr (q := fun c => !eqM (mw (LP i) (cjL' i c)) idP &&
      eqM (powK (mw (LP i) (cjL' i c)) 63) idP)]
  · exact h
  · intro c hc
    have hc' := List.mem_range.1 hc
    simp only []
    rw [(l_inv hc').1, l_el hc', l_el (l_inv hc').2, conjI, mulR_unpackR, mulR_unpackR,
      mulR_unpackR, powRows_unpackR, beqM, beqM]
    rfl

theorem irr_eq {j : ℕ} (hj : j < 512) : irrChoice DQ DL j = irK j := by
  unfold irrChoice irK
  rw [z_eq]
  apply pickSpan_eq
  intro c hc
  rw [(l_inv hc).1, l_el hc, l_el (l_inv hc).2, q_el hj, conjI, mulR_unpackR, mulR_unpackR]
  rfl

theorem t13_all : ∀ j < 512, t13K j = true := by
  intro j hj
  have hc : t13C (j / 8) = true := by
    have hb : j / 8 < 64 := by omega
    generalize j / 8 = b at hb
    interval_cases b
    exacts [t13C0, t13C1, t13C2, t13C3, t13C4, t13C5, t13C6, t13C7, t13C8, t13C9, t13C10, t13C11,
      t13C12, t13C13, t13C14, t13C15, t13C16, t13C17, t13C18, t13C19, t13C20, t13C21, t13C22,
      t13C23, t13C24, t13C25, t13C26, t13C27, t13C28, t13C29, t13C30, t13C31, t13C32, t13C33,
      t13C34, t13C35, t13C36, t13C37, t13C38, t13C39, t13C40, t13C41, t13C42, t13C43, t13C44,
      t13C45, t13C46, t13C47, t13C48, t13C49, t13C50, t13C51, t13C52, t13C53, t13C54, t13C55,
      t13C56, t13C57, t13C58, t13C59, t13C60, t13C61, t13C62, t13C63]
  have h := MatL.allN_iff.1 hc (j % 8) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem a13 : (allLt 512 fun j => DQ.El[j]! == oneR || DQ.El[j]! == z0R ||
    ((irrChoice DQ DL j).all (fun c => decide (c < 504)) &&
      coverOK DQ.El DQ.idx (subProds (irrList DL (irrChoice DQ DL j) DQ.El[j]!)))) = true := by
  refine allLt_iff.2 fun j hj => ?_
  have h := t13_all j hj
  unfold t13K at h
  rw [irr_eq hj, q_el hj, oneR_eq, z_eq, beqM, beqM]
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with h | ⟨ha, hc⟩
  · exact Or.inl h
  · right
    refine ⟨ha, ?_⟩
    have e : irrList DL (irK j) (unpackR 24 (QP j)) =
        ((irK j).map (cjL j) ++ [Zp]).map (unpackR 24) := by
      unfold irrList
      rw [List.map_append, List.map_map]
      refine congrArg₂ (· ++ ·) (List.map_congr_left ?_) (by rw [z_eq]; rfl)
      intro c hcm
      have hc' : c < 504 := by
        have := List.all_eq_true.1 ha c hcm
        simpa using this
      rw [(l_inv hc').1, l_el hc', l_el (l_inv hc').2, conjI, mulR_unpackR, mulR_unpackR]
      rfl
    rw [e, subProds_map]
    exact cover_of hc

theorem comm_eq : commChoice DQ DL = cmK.map fun c => (c / 504, c % 504) := by
  unfold commChoice cmK
  rw [z_eq]
  congr 1
  apply pickSpan_eq
  intro c hc
  have ha : c / 504 < 512 := by omega
  have hb : c % 504 < 504 := Nat.mod_lt _ (by norm_num)
  rw [(q_inv ha).1, (l_inv hb).1, q_el ha, l_el hb, q_el (q_inv ha).2, l_el (l_inv hb).2, commI,
    mulR_unpackR, mulR_unpackR, mulR_unpackR]
  rfl

theorem a14 : ((commChoice DQ DL).all (fun p => decide (p.1 < 512) && decide (p.2 < 504)) &&
    coverOK DQ.El DQ.idx (subProds (commList DQ DL (commChoice DQ DL)))) = true := by
  rw [comm_eq]
  have h := t14
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨ha, hc⟩ := h
  refine ⟨ha, ?_⟩
  generalize cmK.map (fun c => (c / 504, c % 504)) = cs at ha hc ⊢
  have e : commList DQ DL cs = (cs.map (fun p => cmA p.1 p.2) ++ [Zp]).map (unpackR 24) := by
    unfold commList
    rw [List.map_append, List.map_map]
    refine congrArg₂ (· ++ ·) (List.map_congr_left ?_) (by rw [z_eq]; rfl)
    intro p hp
    have hb := List.all_eq_true.1 ha p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨h1, h2⟩ := hb
    rw [(q_inv h1).1, (l_inv h2).1, q_el h1, l_el h2, q_el (q_inv h1).2, l_el (l_inv h2).2, commI,
      mulR_unpackR, mulR_unpackR, mulR_unpackR]
    rfl
  rw [e, subProds_map]
  exact cover_of hc

theorem a15 : (allLt 512 fun i => allLt qGens.size fun k =>
    conjI DQ.El[i]! DQ.El[DQ.inv[i]!]! qGens[k]! == qGens[k]! ||
      conjI DQ.El[i]! DQ.El[DQ.inv[i]!]! qGens[k]! == mulR qGens[k]! z0R) = true := by
  rw [qg_size]
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun k hk => ?_
  rw [(q_inv hi).1, q_el hi, q_el (q_inv hi).2, qg_eq k hk, z_eq, conjI, mulR_unpackR,
    mulR_unpackR, mulR_unpackR, beqM, beqM]
  exact MatL.allN_iff.1 (MatL.allN_iff.1 t15 i hi) k hk

theorem a16 : (allLt 504 fun i => DL.El[i]! == oneR || (List.range qGens.size).any fun k =>
    !(conjI DL.El[i]! DL.El[DL.inv[i]!]! qGens[k]! == qGens[k]!) &&
      !(conjI DL.El[i]! DL.El[DL.inv[i]!]! qGens[k]! == mulR qGens[k]! z0R)) = true := by
  refine allLt_iff.2 fun i hi => ?_
  have h := MatL.allN_iff.1 t16 i hi
  rw [qg_size, l_el hi, oneR_eq, beqM]
  rw [any_congr (q := fun k => !eqM (mw (mw (LP i) (QG k)) (LP (LInv i))) (QG k) &&
      !eqM (mw (mw (LP i) (QG k)) (LP (LInv i))) (mw (QG k) Zp))]
  · exact h
  · intro k hk
    have hk' := List.mem_range.1 hk
    rw [(l_inv hi).1, l_el (l_inv hi).2, qg_eq k hk', z_eq, conjI, mulR_unpackR,
      mulR_unpackR, mulR_unpackR, beqM, beqM]
    rfl

open CFSG.LargeExtraspecial.S63 in
theorem c21112 : d4ACheck = true := by
  unfold d4ACheck
  rw [dq_eq, dl_eq]
  unfold d4ACheckOn
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨gens_q, gens_l⟩, ok_of_K qg_size qg_eq repQ closQ⟩,
    invOK_of_K qg_size qg_eq repQ invQ⟩, ok_of_K lg_size lg_eq repL closL⟩,
    invOK_of_K lg_size lg_eq repL invL⟩, comm_q⟩, comm_l⟩, mem_z⟩, a10⟩, a11⟩, a12⟩, a13⟩,
    by simpa only [Bool.and_eq_true] using a14⟩, a15⟩, a16⟩

end CertificateChecks.KernelS63.A21112

end
