
module

public import Certificates.Kernel.SporSch.PairJ3.CntSmall
public import Certificates.Kernel.SporSch.PairJ3.CntSrch
public import Certificates.Kernel.SporSch.PairJ3.CntScan0
public import Certificates.Kernel.SporSch.PairJ3.CntScan1
public import Certificates.Kernel.SporSch.PairJ3.CntInv1
public import Certificates.Kernel.SporSch.PairJ3.CntGroup
public import Certificates.Kernel.SporSch.PairJ3.Check2237
public import CFSG.Certificates.Kernel.SporSch.Srch4Proof
public import CFSG.Sporadic.Schreier.PairJ3PairsBase

public section

namespace CertificateChecks.KernelSporSch.PJ3Count

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PJ3Group

noncomputable abbrev P3 : Subgroup (Equiv.Perm (Fin 6156)) := j3Chain.originalSubgroup

theorem tc : TabChain 6156 13 5 4 PJ3.BP 97 64 PJ3T.NR PJ3T.NR 61 1024 7 1024 PJ3.S PJ3.SI PJ3.LR
    PJ3T.Ts PJ3T.LT PJ3T.PT PJ3T.QT j3StrongArrs PairJ3.baseArr PairJ3.bs :=
  ⟨PJ3Check.binds, PJ3Check.perm, PJ3.ho, by decide, PJ3Check.tabs, rfl⟩

noncomputable abbrev E (F : Nat) : Equiv.Perm (Fin 6156) :=
  nfElt 6156 j3StrongArrs PairJ3.baseArr (nfArr 4 F)

theorem E_rep {F : Nat} (hF : nfValidK 4 PJ3.LR F = true) : RepF 6156 (PJ3Cn.nfp F) (E F) :=
  (nfPtT_sound tc hF).2

theorem chunk_sum (m B : Nat) (f V : Nat → Nat)
    (h : ∀ q < m, sumN B (fun j => f (Nat.add (Nat.mul q B) j)) = V q) :
    sumN (m * B) f = sumN m V := by
  rw [sumN_mul, sumN_eq, sumN_eq]
  exact congrArg List.sum (List.map_congr_left fun q hq => h q (List.mem_range.1 hq))

theorem split66 {q : Nat} : Nat.add (Nat.mul (q / 6) 6) (q % 6) = q := by
  change q / 6 * 6 + q % 6 = q
  omega

theorem split44 {q : Nat} : Nat.add (Nat.mul (q / 4) 4) (q % 4) = q := by
  change q / 4 * 4 + q % 4 = q
  omega

theorem sumN_finset (m : Nat) (f : Nat → Nat) : sumN m f = ∑ i ∈ Finset.range m, f i := by
  rw [sumN_eq, Finset.sum_range, ← List.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

theorem keyL_congr (n : Nat) {f g : Nat → Nat} :
    ∀ {bs : List Nat}, (∀ b ∈ bs, f b = g b) → keyL n f bs = keyL n g bs
  | [], _ => rfl
  | b :: bs, h => by
    change strictN (keyL n f bs) (fun r => Nat.add (f b) (Nat.mul n r)) =
      strictN (keyL n g bs) (fun r => Nat.add (g b) (Nat.mul n r))
    rw [strictN_val, strictN_val, keyL_congr n fun c hc => h c (List.mem_cons_of_mem b hc),
      h b List.mem_cons_self]

section J3

theorem hH : BaseFaithful P3 PairJ3.bs := j3_baseFaithful

theorem hbs : ∀ b ∈ PairJ3.bs, b < 6156 := j3_bs_lt

theorem E_mem {F : Nat} (hF : nfValidK 4 PJ3.LR F = true) : E F ∈ P3 :=
  nfElt_mem j3ChainArrays (chainCheckFacts PairJ3.chain_check.1) j3Chain_valid.1
    (nfPtT_sound tc hF).1

theorem card_P3 : Nat.card P3 = 50232960 := by
  rw [P3, ← j3P_eq_original]
  exact card_j3P

theorem srch_eq {X Y : Nat → Nat} {x y : Equiv.Perm (Fin 6156)} (hX : RepF 6156 X x)
    (hY : RepF 6156 Y y) (hx : x ∈ P3) (hy : y ∈ P3) (h01 : X 0 = 1) {V : Nat → Nat}
    (hV : ∀ g < 6, ∀ r < 6, Nat.beq (PJ3Cn.srAt X Y (Nat.add (Nat.mul g 6) r))
      (V (Nat.add (Nat.mul g 6) r)) = true) :
    Nat.card {g : P3 // (g : Equiv.Perm (Fin 6156)) * x = y * g} = sumN 36 V := by
  have h := Tab.srch4_proved (b0 := 0) (b1 := 1) (bs := [3, 2]) j3ChainArrays
    PairJ3.chain_check.1 (by norm_num) tc hX hY hx hy h01
  rw [← h, Nat.eq_of_beq_eq_true PJ3Cn.c0]
  refine chunk_sum 36 171 _ V fun q hq => ?_
  have := Nat.eq_of_beq_eq_true (hV (q / 6) (by omega) (q % 6) (Nat.mod_lt _ (by norm_num)))
  rw [split66] at this
  exact this

theorem repsF : nfValidK 4 PJ3.LR PJ3N.nT = true ∧ nfValidK 4 PJ3.LR PJ3N.nYA = true ∧
    nfValidK 4 PJ3.LR PJ3N.nYB = true ∧ nfValidK 4 PJ3.LR PJ3N.nZ = true ∧
    nfValidK 4 PJ3.LR PJ3N.nNu = true ∧ ordPL PJ3Cn.bs PJ3Cn.tP 2 = true ∧
    ordPL PJ3Cn.bs PJ3Cn.aP 3 = true ∧ ordPL PJ3Cn.bs PJ3Cn.bP 3 = true ∧
    ordPL PJ3Cn.bs PJ3Cn.zP 19 = true ∧ Nat.beq (PJ3Cn.tP 0) 1 = true ∧
    Nat.beq (PJ3Cn.aP 0) 1 = true ∧ Nat.beq (PJ3Cn.bP 0) 1 = true ∧
    Nat.beq (PJ3Cn.zP 0) 1 = true ∧ eqOnL PJ3Cn.bs (fun b => PJ3Cn.nfp PJ3N.nNu (PJ3Cn.zP b))
      (fun b => powF PJ3Cn.zP 4 (PJ3Cn.nfp PJ3N.nNu b)) = true := by
  have h := PJ3Cn.reps
  unfold PJ3Cn.repsB at h
  simpa only [bAnd_iff] using h

theorem bindAll {g : Nat} (hg : g < 4) {F P : Nat}
    (hFP : ∀ r, PJ3Cn.bindB g r = PJ3Cn.bindR F P (Nat.mul r 1026)) :
    ∀ x < 6156, bindAt 6156 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT F P x = true := by
  intro x hx
  have h := PJ3Cn.bindB_all g hg (x / 1026) (by change x / 1026 < 6; omega)
  rw [hFP] at h
  have h2 := allBlk_spec h (x % 1026) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 1026) 1026) (x % 1026) = x := by
    change x / 1026 * 1026 + x % 1026 = x
    omega
  rwa [e] at h2

noncomputable abbrev tE : Equiv.Perm (Fin 6156) := E PJ3N.nT
noncomputable abbrev aE : Equiv.Perm (Fin 6156) := E PJ3N.nYA
noncomputable abbrev bE : Equiv.Perm (Fin 6156) := E PJ3N.nYB
noncomputable abbrev zE : Equiv.Perm (Fin 6156) := E PJ3N.nZ
noncomputable abbrev nuE : Equiv.Perm (Fin 6156) := E PJ3N.nNu

theorem tRep : RepF 6156 PJ3Cn.tP tE :=
  bind_spec tc repsF.1 (bindAll (g := 0) (by norm_num) fun _ => rfl)
theorem aRep : RepF 6156 PJ3Cn.aP aE :=
  bind_spec tc repsF.2.1 (bindAll (g := 1) (by norm_num) fun _ => rfl)
theorem bRep : RepF 6156 PJ3Cn.bP bE :=
  bind_spec tc repsF.2.2.1 (bindAll (g := 2) (by norm_num) fun _ => rfl)
theorem zRep : RepF 6156 PJ3Cn.zP zE :=
  bind_spec tc repsF.2.2.2.1 (bindAll (g := 3) (by norm_num) fun _ => rfl)

theorem tMem : tE ∈ P3 := E_mem repsF.1
theorem aMem : aE ∈ P3 := E_mem repsF.2.1
theorem bMem : bE ∈ P3 := E_mem repsF.2.2.1
theorem zMem : zE ∈ P3 := E_mem repsF.2.2.2.1
theorem nuMem : nuE ∈ P3 := E_mem repsF.2.2.2.2.1

theorem tOrd : orderOf tE = 2 :=
  (ordPL_iff hH hbs tRep tMem Nat.prime_two).1 repsF.2.2.2.2.2.1
theorem aOrd : orderOf aE = 3 :=
  (ordPL_iff hH hbs aRep aMem Nat.prime_three).1 repsF.2.2.2.2.2.2.1
theorem bOrd : orderOf bE = 3 :=
  (ordPL_iff hH hbs bRep bMem Nat.prime_three).1 repsF.2.2.2.2.2.2.2.1
theorem zOrd : orderOf zE = 19 :=
  (ordPL_iff hH hbs zRep zMem (by norm_num)).1 repsF.2.2.2.2.2.2.2.2.1

theorem nuEq : nuE * zE = zE ^ 4 * nuE :=
  eq_of_eqOnL hH ((E_rep repsF.2.2.2.2.1).comp zRep) ((zRep.powF 4).comp (E_rep repsF.2.2.2.2.1))
    (P3.mul_mem nuMem zMem) (P3.mul_mem (P3.pow_mem zMem 4) nuMem) repsF.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem cent_t : Nat.card {g : P3 // (g : Equiv.Perm (Fin 6156)) * tE = tE * g} = 1920 := by
  rw [srch_eq tRep tRep tMem tMem (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.1)
    PJ3Cn.srT_all]
  exact Nat.eq_of_beq_eq_true PJ3Cn.vT

theorem cent_a : Nat.card {g : P3 // (g : Equiv.Perm (Fin 6156)) * aE = aE * g} = 1080 := by
  rw [srch_eq aRep aRep aMem aMem (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.1)
    PJ3Cn.srA_all]
  exact Nat.eq_of_beq_eq_true PJ3Cn.vA

theorem cent_b : Nat.card {g : P3 // (g : Equiv.Perm (Fin 6156)) * bE = bE * g} = 243 := by
  rw [srch_eq bRep bRep bMem bMem (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.2.1)
    PJ3Cn.srB_all]
  exact Nat.eq_of_beq_eq_true PJ3Cn.vB

theorem cent_z : Nat.card {g : P3 // (g : Equiv.Perm (Fin 6156)) * zE = zE * g} = 19 := by
  rw [srch_eq zRep zRep zMem zMem (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.2.2.1)
    PJ3Cn.srZ_all]
  exact Nat.eq_of_beq_eq_true PJ3Cn.vZ

theorem cent_zz : Nat.card {g : P3 // (g : Equiv.Perm (Fin 6156)) * zE = (zE * zE) * g} = 0 := by
  rw [srch_eq zRep (zRep.comp zRep) zMem (P3.mul_mem zMem zMem)
    (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.2.2.1) PJ3Cn.srZ2_all]
  exact Nat.eq_of_beq_eq_true PJ3Cn.vZ2

abbrev mk (x : Equiv.Perm (Fin 6156)) (hx : x ∈ P3) : P3 := ⟨x, hx⟩

theorem card_K : Nat.card P3 = 50232960 := card_P3

theorem cent_K (x : P3) {N : Nat}
    (h : Nat.card {g : P3 // (g : Equiv.Perm (Fin 6156)) * x = x * g} = N) :
    Nat.card {g : P3 // g * x = x * g} = N := by
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => Subtype.ext_iff)

theorem card_class (x : P3) {N : Nat}
    (h : Nat.card {g : P3 // (g : Equiv.Perm (Fin 6156)) * x = x * g} = N) (hN : 0 < N) :
    Nat.card {y : P3 // IsConj x y} = 50232960 / N := by
  have h2 := card_class_mul x
  rw [cent_K x h, card_K] at h2
  rw [← h2, Nat.mul_div_cancel _ hN]

theorem orderOf_conj (c x : P3) : orderOf (c * x * c⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem orderOf_of_isConj {x y : P3} (h : IsConj x y) : orderOf y = orderOf x := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact orderOf_conj c x

theorem isConj_of_eq {d y r : P3} (h : d * y = r * d) : IsConj y r :=
  isConj_iff.2 ⟨d, by rw [h, mul_inv_cancel_right]⟩

theorem s2_row {i : Nat} (hi : i < 128) : PJ3Cn.s2At i = true := by
  have h0 : allBlk (Nat.mul (Nat.add (Nat.mul (i / 32) 4) (i / 8 % 4)) 8) PJ3Cn.s2At 8 = true :=
    PJ3Cn.s2B_all (i / 32) (by change i / 32 < 4; omega) (i / 8 % 4)
      (by change i / 8 % 4 < 4; omega)
  have h := allBlk_spec h0 (i % 8) (by omega)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (i / 32) 4) (i / 8 % 4)) 8) (i % 8) = i := by
    change (i / 32 * 4 + i / 8 % 4) * 8 + i % 8 = i
    omega
  rwa [e] at h

theorem s2_parts {i : Nat} (hi : i < 128) :
    nfValidK 4 PJ3.LR (PJ3Cn.r2 i) = true ∧
    (∀ j < 128, PJ3Cn.m2 i j < 128 ∧ eqOnL PJ3Cn.bs
      (fun b => PJ3Cn.nfp (PJ3Cn.r2 i) (PJ3Cn.nfp (PJ3Cn.r2 j) b))
      (PJ3Cn.nfp (PJ3Cn.r2 (PJ3Cn.m2 i j))) = true) ∧
    (∀ j < 128, i < j → eqOnL PJ3Cn.bs (PJ3Cn.nfp (PJ3Cn.r2 i)) (PJ3Cn.nfp (PJ3Cn.r2 j)) = false) ∧
    (ordPL PJ3Cn.bs (PJ3Cn.nfp (PJ3Cn.r2 i)) 2 = true → nfValidK 4 PJ3.LR (PJ3Cn.d2 i) = true ∧
      eqOnL PJ3Cn.bs (fun b => PJ3Cn.nfp (PJ3Cn.d2 i) (PJ3Cn.tP b))
        (fun b => PJ3Cn.nfp (PJ3Cn.r2 i) (PJ3Cn.nfp (PJ3Cn.d2 i) b)) = true) := by
  have h := s2_row hi
  unfold PJ3Cn.s2At at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun j hj => ?_, fun j hj hij => ?_, fun ho => ?_⟩
  · have := allN_spec h2 j hj
    rw [bAnd_iff] at this
    exact ⟨by simpa [Nat.blt_eq] using this.1, this.2⟩
  · have := allN_spec h3 j hj
    rw [blt_true hij] at this
    cases e : eqOnL PJ3Cn.bs (PJ3Cn.nfp (PJ3Cn.r2 i)) (PJ3Cn.nfp (PJ3Cn.r2 j))
    · rfl
    · rw [e] at this
      exact absurd this (by decide)
  · rw [ho, bAnd_iff] at h4
    exact h4

noncomputable abbrev r2E (i : Nat) : Equiv.Perm (Fin 6156) := E (PJ3Cn.r2 i)

theorem r2_mem {i : Nat} (hi : i < 128) : r2E i ∈ P3 := E_mem (s2_parts hi).1

theorem r2_mul {i j : Nat} (hi : i < 128) (hj : j < 128) :
    r2E i * r2E j = r2E (PJ3Cn.m2 i j) := by
  obtain ⟨hm, he⟩ := (s2_parts hi).2.1 j hj
  exact eq_of_eqOnL hH ((E_rep (s2_parts hi).1).comp (E_rep (s2_parts hj).1))
    (E_rep (s2_parts hm).1) (P3.mul_mem (r2_mem hi) (r2_mem hj)) (r2_mem hm) he

theorem r2_inj {i j : Nat} (hi : i < 128) (hj : j < 128) (h : r2E i = r2E j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hij | hij
  · have h1 := (s2_parts hi).2.2.1 j hj hij
    rw [eqOnL_of_eq (bs := PJ3Cn.bs) hbs (E_rep (s2_parts hi).1)
      ((E_rep (s2_parts hj).1).congr h.symm)] at h1
    exact absurd h1 (by decide)
  · have h1 := (s2_parts hj).2.2.1 i hi hij
    rw [eqOnL_of_eq (bs := PJ3Cn.bs) hbs (E_rep (s2_parts hj).1)
      ((E_rep (s2_parts hi).1).congr h)] at h1
    exact absurd h1 (by decide)

def s2Set : Set P3 := {g | ∃ i < 128, (g : Equiv.Perm (Fin 6156)) = r2E i}

theorem s2_closed : ∀ a ∈ s2Set, ∀ b ∈ s2Set, a * b ∈ s2Set := by
  rintro a ⟨i, hi, ha⟩ b ⟨j, hj, hb⟩
  exact ⟨PJ3Cn.m2 i j, ((s2_parts hi).2.1 j hj).1, by
    rw [Subgroup.coe_mul, ha, hb, r2_mul hi hj]⟩

noncomputable def S2 : Subgroup P3 :=
  mulClosed s2Set s2_closed (mk (r2E 0) (r2_mem (by norm_num))) ⟨0, by norm_num, rfl⟩

theorem card_S2 : Nat.card S2 = 128 := by
  have hb : Function.Bijective (fun i : Fin 128 =>
      (⟨mk (r2E i) (r2_mem i.2), mem_mulClosed.2 ⟨i, i.2, rfl⟩⟩ : S2)) := by
    refine ⟨fun i j h => Fin.ext (r2_inj i.2 j.2 ?_), fun g => ?_⟩
    · have := congrArg (fun g : S2 => ((g : P3) : Equiv.Perm (Fin 6156))) h
      exact this
    · obtain ⟨i, hi, he⟩ := mem_mulClosed.1 g.2
      exact ⟨⟨i, hi⟩, Subtype.ext (Subtype.ext he.symm)⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_fin]

theorem fact2 : (Nat.card P3).factorization 2 = 7 :=
  factorization_eq Nat.prime_two (m := 392445) (by norm_num) (by rw [card_K]; norm_num)

theorem fact3 : (Nat.card P3).factorization 3 = 5 :=
  factorization_eq Nat.prime_three (m := 206720) (by norm_num) (by rw [card_K]; norm_num)

theorem fact19 : (Nat.card P3).factorization 19 = 1 :=
  factorization_eq (by norm_num) (m := 2643840) (by norm_num) (by rw [card_K]; norm_num)

noncomputable abbrev tK : P3 := mk tE tMem

theorem invol_conj {x : P3} (hx : orderOf x = 2) : IsConj tK x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_conj_mem S2 (by rw [card_S2, fact2]; norm_num) (k := 1)
    (by rw [hx, pow_one])
  obtain ⟨i, hi, he⟩ := mem_mulClosed.1 hg
  have ho : orderOf (r2E i) = 2 := by
    rw [← he, Subgroup.orderOf_coe, orderOf_conj, hx]
  obtain ⟨hd, heq⟩ := (s2_parts hi).2.2.2
    ((ordPL_iff hH hbs (E_rep (s2_parts hi).1) (r2_mem hi) Nat.prime_two).2 ho)
  have hD := E_mem hd
  have h1 : E (PJ3Cn.d2 i) * tE = r2E i * E (PJ3Cn.d2 i) :=
    eq_of_eqOnL hH ((E_rep hd).comp tRep) ((E_rep (s2_parts hi).1).comp (E_rep hd))
      (P3.mul_mem hD tMem) (P3.mul_mem (r2_mem hi) hD) heq
  have h2 : IsConj tK (g * x * g⁻¹) :=
    isConj_of_eq (d := mk _ hD) (r := g * x * g⁻¹) (Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, he]
      exact h1))
  exact h2.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)

theorem card_two : Nat.card {x : P3 // orderOf x = 2} = 26163 := by
  have e : {x : P3 // orderOf x = 2} ≃ {y : P3 // IsConj tK y} :=
    Equiv.subtypeEquivRight fun x => ⟨invol_conj, fun h => by
      rw [orderOf_of_isConj h, Subgroup.orderOf_mk]
      exact tOrd⟩
  rw [Nat.card_congr e, card_class tK cent_t (by norm_num)]

theorem s3_row {i : Nat} (hi : i < 243) : PJ3Cn.s3At i = true := by
  have h0 : allBlk (Nat.mul (Nat.add (Nat.mul (i / 81) 3) (i / 27 % 3)) 27) PJ3Cn.s3At 27 = true :=
    PJ3Cn.s3B_all (i / 81) (by change i / 81 < 3; omega) (i / 27 % 3)
      (by change i / 27 % 3 < 3; omega)
  have h := allBlk_spec h0 (i % 27) (by omega)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (i / 81) 3) (i / 27 % 3)) 27) (i % 27) = i := by
    change (i / 81 * 3 + i / 27 % 3) * 27 + i % 27 = i
    omega
  rwa [e] at h

theorem s3_parts {i : Nat} (hi : i < 243) :
    nfValidK 4 PJ3.LR (PJ3Cn.r3 i) = true ∧
    eqOnL PJ3Cn.bs (fun b => PJ3Cn.nfp (PJ3Cn.r3 i) (PJ3Cn.bP b))
      (fun b => PJ3Cn.bP (PJ3Cn.nfp (PJ3Cn.r3 i) b)) = true ∧
    (∀ j < 243, i < j → eqOnL PJ3Cn.bs (PJ3Cn.nfp (PJ3Cn.r3 i)) (PJ3Cn.nfp (PJ3Cn.r3 j)) = false) ∧
    (ordPL PJ3Cn.bs (PJ3Cn.nfp (PJ3Cn.r3 i)) 3 = true → nfValidK 4 PJ3.LR (PJ3Cn.d3 i) = true ∧
      eqOnL PJ3Cn.bs (fun b => PJ3Cn.nfp (PJ3Cn.d3 i) (PJ3Cn.ySel (PJ3Cn.c3 i) b))
        (fun b => PJ3Cn.nfp (PJ3Cn.r3 i) (PJ3Cn.nfp (PJ3Cn.d3 i) b)) = true) := by
  have h := s3_row hi
  unfold PJ3Cn.s3At at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun j hj hij => ?_, fun ho => ?_⟩
  · have := allN_spec h3 j hj
    rw [blt_true hij] at this
    cases e : eqOnL PJ3Cn.bs (PJ3Cn.nfp (PJ3Cn.r3 i)) (PJ3Cn.nfp (PJ3Cn.r3 j))
    · rfl
    · rw [e] at this
      exact absurd this (by decide)
  · rw [ho, bAnd_iff] at h4
    exact h4

noncomputable abbrev r3E (i : Nat) : Equiv.Perm (Fin 6156) := E (PJ3Cn.r3 i)

theorem r3_mem {i : Nat} (hi : i < 243) : r3E i ∈ P3 := E_mem (s3_parts hi).1

theorem r3_comm {i : Nat} (hi : i < 243) : r3E i * bE = bE * r3E i :=
  eq_of_eqOnL hH ((E_rep (s3_parts hi).1).comp bRep) (bRep.comp (E_rep (s3_parts hi).1))
    (P3.mul_mem (r3_mem hi) bMem) (P3.mul_mem bMem (r3_mem hi)) (s3_parts hi).2.1

theorem r3_inj {i j : Nat} (hi : i < 243) (hj : j < 243) (h : r3E i = r3E j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hij | hij
  · have h1 := (s3_parts hi).2.2.1 j hj hij
    rw [eqOnL_of_eq (bs := PJ3Cn.bs) hbs (E_rep (s3_parts hi).1)
      ((E_rep (s3_parts hj).1).congr h.symm)] at h1
    exact absurd h1 (by decide)
  · have h1 := (s3_parts hj).2.2.1 i hi hij
    rw [eqOnL_of_eq (bs := PJ3Cn.bs) hbs (E_rep (s3_parts hj).1)
      ((E_rep (s3_parts hi).1).congr h)] at h1
    exact absurd h1 (by decide)

noncomputable abbrev aK : P3 := mk aE aMem
noncomputable abbrev bK : P3 := mk bE bMem

theorem card_C3 : Nat.card (Subgroup.centralizer {bK}) = 243 := by
  rw [← cent_K bK cent_b]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => Subgroup.mem_centralizer_singleton_iff)

theorem r3_cover (g : Subgroup.centralizer {bK}) : ∃ i < 243, ((g : P3) : Equiv.Perm (Fin 6156)) =
    r3E i := by
  let f : Fin 243 → Subgroup.centralizer {bK} := fun i => ⟨mk (r3E i) (r3_mem i.2),
    Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (r3_comm i.2))⟩
  have hinj : Function.Injective f := fun i j h => Fin.ext (r3_inj i.2 j.2
    (congrArg (fun g : Subgroup.centralizer {bK} => ((g : P3) : Equiv.Perm (Fin 6156))) h))
  obtain ⟨i, hi⟩ := (hinj.bijective_of_nat_card_le (by rw [card_C3, Nat.card_fin])).2 g
  exact ⟨i, i.2, by rw [← hi]⟩

theorem ySel_rep (c : Nat) : RepF 6156 (PJ3Cn.ySel c) (if c = 0 then aE else bE) := by
  intro x hx
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left rfl]
    exact aRep x hx
  · rw [ite_eq_right hc]
    have : Nat.beq c 0 = false := by
      cases h : Nat.beq c 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hc
    change Bool.rec (motive := fun _ => Nat) (PJ3Cn.bP x) (PJ3Cn.aP x) (Nat.beq c 0) = _
    rw [this]
    exact bRep x hx

theorem ord3_conj {x : P3} (hx : orderOf x = 3) : IsConj aK x ∨ IsConj bK x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_mem (Subgroup.centralizer {bK}) (by rw [card_C3, fact3]; norm_num)
    (k := 1) (by rw [hx, pow_one])
  obtain ⟨i, hi, he⟩ := r3_cover ⟨_, hg⟩
  have ho : orderOf (r3E i) = 3 := by
    rw [← he, Subgroup.orderOf_coe, orderOf_conj, hx]
  obtain ⟨hd, heq⟩ := (s3_parts hi).2.2.2
    ((ordPL_iff hH hbs (E_rep (s3_parts hi).1) (r3_mem hi) Nat.prime_three).2 ho)
  have hD := E_mem hd
  have hY : (if PJ3Cn.c3 i = 0 then aE else bE) ∈ P3 := by
    split
    · exact aMem
    · exact bMem
  have h1 := eq_of_eqOnL hH ((E_rep hd).comp (ySel_rep (PJ3Cn.c3 i)))
    ((E_rep (s3_parts hi).1).comp (E_rep hd)) (P3.mul_mem hD hY) (P3.mul_mem (r3_mem hi) hD) heq
  have hb : IsConj (g * x * g⁻¹) x := isConj_iff.2 ⟨g⁻¹, by group⟩
  by_cases hc : PJ3Cn.c3 i = 0
  · rw [ite_eq_left hc] at h1
    refine Or.inl ((isConj_of_eq (d := mk _ hD) (r := g * x * g⁻¹) (Subtype.ext ?_)).trans hb)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, he]
    exact h1
  · rw [ite_eq_right hc] at h1
    refine Or.inr ((isConj_of_eq (d := mk _ hD) (r := g * x * g⁻¹) (Subtype.ext ?_)).trans hb)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, he]
    exact h1

theorem not_conj_ab : ¬IsConj aK bK := by
  intro h
  have e : {y : P3 // IsConj aK y} ≃ {y : P3 // IsConj bK y} :=
    Equiv.subtypeEquivRight fun y => ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩
  have h1 := card_class aK cent_a (by norm_num)
  have h2 := card_class bK cent_b (by norm_num)
  rw [Nat.card_congr e, h2] at h1
  norm_num at h1

theorem card_three : Nat.card {x : P3 // orderOf x = 3} = 253232 := by
  have e : {x : P3 // orderOf x = 3} ≃ {y : P3 // IsConj aK y ∨ IsConj bK y} :=
    Equiv.subtypeEquivRight fun x => ⟨ord3_conj, fun h => by
      rcases h with h | h
      · rw [orderOf_of_isConj h, Subgroup.orderOf_mk]
        exact aOrd
      · rw [orderOf_of_isConj h, Subgroup.orderOf_mk]
        exact bOrd⟩
  have hd : Disjoint (fun y : P3 => IsConj aK y) (fun y => IsConj bK y) := by
    rw [Pi.disjoint_iff]
    intro y
    rw [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩
    exact not_conj_ab (h1.trans h2.symm)
  classical
  rw [Nat.card_congr (e.trans (subtypeOrEquiv _ _ hd)), Nat.card_sum,
    card_class aK cent_a (by norm_num), card_class bK cent_b (by norm_num)]

noncomputable abbrev zK : P3 := mk zE zMem
noncomputable abbrev nuK : P3 := mk nuE nuMem

theorem zK_ord : orderOf zK = 19 := by
  rw [Subgroup.orderOf_mk]
  exact zOrd

theorem nuK_eq : nuK * zK * nuK⁻¹ = zK ^ 4 := by
  have h : nuK * zK = zK ^ 4 * nuK := Subtype.ext nuEq
  rw [h, mul_inv_cancel_right]

theorem conj4 (m : Nat) : IsConj (zK ^ m) (zK ^ (4 * m % 19)) :=
  isConj_iff.2 ⟨nuK, by rw [← conj_pow, nuK_eq, ← pow_mul, ← zK_ord, pow_mod_orderOf]⟩

theorem conj4_iter (m : Nat) : ∀ j, IsConj (zK ^ m) (zK ^ (4 ^ j * m % 19))
  | 0 => by
    rw [pow_zero, one_mul, ← zK_ord, pow_mod_orderOf]
  | j + 1 => by
    refine (conj4_iter m j).trans ?_
    have e : 4 ^ (j + 1) * m % 19 = 4 * (4 ^ j * m % 19) % 19 := by
      have e1 : 4 ^ (j + 1) * m = 4 * (4 ^ j * m) := by ring
      rw [e1, Nat.mul_mod, Nat.mul_mod 4 (4 ^ j * m % 19), Nat.mod_mod]
    rw [e]
    exact conj4 _

theorem pow_conj {k : Nat} (hk : k < 19) (hk0 : k ≠ 0) :
    IsConj zK (zK ^ k) ∨ IsConj (zK ^ 2) (zK ^ k) := by
  have c1 : ∀ j k, 4 ^ j * 1 % 19 = k → IsConj zK (zK ^ k) := fun j k hk => by
    have := conj4_iter 1 j
    rwa [pow_one, hk] at this
  have c2 : ∀ j k, 4 ^ j * 2 % 19 = k → IsConj (zK ^ 2) (zK ^ k) := fun j k hk => by
    have := conj4_iter 2 j
    rwa [hk] at this
  interval_cases k
  · exact absurd rfl hk0
  · exact Or.inl (c1 0 _ (by norm_num))
  · exact Or.inr (c2 0 _ (by norm_num))
  · exact Or.inr (c2 6 _ (by norm_num))
  · exact Or.inl (c1 1 _ (by norm_num))
  · exact Or.inl (c1 8 _ (by norm_num))
  · exact Or.inl (c1 7 _ (by norm_num))
  · exact Or.inl (c1 3 _ (by norm_num))
  · exact Or.inr (c2 1 _ (by norm_num))
  · exact Or.inl (c1 4 _ (by norm_num))
  · exact Or.inr (c2 8 _ (by norm_num))
  · exact Or.inl (c1 6 _ (by norm_num))
  · exact Or.inr (c2 7 _ (by norm_num))
  · exact Or.inr (c2 2 _ (by norm_num))
  · exact Or.inr (c2 3 _ (by norm_num))
  · exact Or.inr (c2 5 _ (by norm_num))
  · exact Or.inl (c1 2 _ (by norm_num))
  · exact Or.inl (c1 5 _ (by norm_num))
  · exact Or.inr (c2 4 _ (by norm_num))

theorem ord19_conj {x : P3} (hx : orderOf x = 19) : IsConj zK x ∨ IsConj (zK ^ 2) x := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_conj_mem (Subgroup.zpowers zK)
    (by rw [Nat.card_zpowers, zK_ord, fact19, pow_one]) (k := 1) (by rw [hx, pow_one])
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hg
  obtain ⟨k, hk⟩ := hg
  have hk' : zK ^ (k % 19) = g * x * g⁻¹ := by rw [← zK_ord, pow_mod_orderOf, hk]
  have hk0 : k % 19 ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk'
    have := orderOf_conj g x
    rw [← hk', orderOf_one, hx] at this
    norm_num at this
  have hb : IsConj (g * x * g⁻¹) x := isConj_iff.2 ⟨g⁻¹, by group⟩
  rcases pow_conj (Nat.mod_lt k (by norm_num)) hk0 with h | h
  · exact Or.inl ((hk' ▸ h).trans hb)
  · exact Or.inr ((hk' ▸ h).trans hb)

theorem not_conj_z : ¬IsConj zK (zK ^ 2) := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hc' : (c : Equiv.Perm (Fin 6156)) * zE = (zE * zE) * c := by
    have : c * zK = zK ^ 2 * c := by rw [← hc, inv_mul_cancel_right]
    have := congrArg Subtype.val this
    rw [pow_two] at this
    exact this
  have hne : Nonempty {g : P3 // (g : Equiv.Perm (Fin 6156)) * zE = (zE * zE) * g} := ⟨⟨c, hc'⟩⟩
  have := Nat.card_pos (α := {g : P3 // (g : Equiv.Perm (Fin 6156)) * zE = (zE * zE) * g})
  rw [cent_zz] at this
  exact absurd this (lt_irrefl 0)

theorem cent_zz2 : Nat.card {g : P3 // (g : Equiv.Perm (Fin 6156)) * (zK ^ 2 : P3) =
    (zK ^ 2 : P3) * g} = 19 := by
  rw [← cent_K zK cent_z]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, Subtype.val_inj]
  change Commute g (zK ^ 2) ↔ Commute g zK
  have e : (zK ^ 2) ^ 10 = zK := by
    rw [← pow_mul, ← pow_mod_orderOf, zK_ord]
    norm_num
  constructor
  · intro h
    have := h.pow_right 10
    rwa [e] at this
  · intro h
    exact h.pow_right 2

theorem card_nineteen : Nat.card {x : P3 // orderOf x = 19} = 5287680 := by
  have hz2 : orderOf (zK ^ 2) = 19 := by
    rw [Nat.Coprime.orderOf_pow (by rw [zK_ord]; norm_num), zK_ord]
  have e : {x : P3 // orderOf x = 19} ≃ {y : P3 // IsConj zK y ∨ IsConj (zK ^ 2) y} :=
    Equiv.subtypeEquivRight fun x => ⟨ord19_conj, fun h => by
      rcases h with h | h
      · rw [orderOf_of_isConj h, zK_ord]
      · rw [orderOf_of_isConj h, hz2]⟩
  have hd : Disjoint (fun y : P3 => IsConj zK y) (fun y => IsConj (zK ^ 2) y) := by
    rw [Pi.disjoint_iff]
    intro y
    rw [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩
    exact not_conj_z (h1.trans h2.symm)
  classical
  rw [Nat.card_congr (e.trans (subtypeOrEquiv _ _ hd)), Nat.card_sum,
    card_class zK cent_z (by norm_num), card_class (zK ^ 2) cent_zz2 (by norm_num)]

theorem cSz : PJ3T.c = 26163 := Nat.eq_of_beq_eq_true PJ3Cl.cSz

noncomputable abbrev xE (i : Nat) : Equiv.Perm (Fin 6156) := E (nfX 4 (PJ3Cl.X i))

theorem inv_rec {i : Nat} (hi : i < 26163) :
    nfValidK 4 PJ3.LR (nfX 4 (PJ3Cl.X i)) = true ∧ orderOf (xE i) = 2 := by
  have h0 : allBlk (Nat.mul (Nat.add (Nat.mul (i / 2048) 4) (i / 512 % 4)) 512)
      (invAt 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT PJ3.LR PJ3Cn.bs PJ3T.c PJ3Cl.X) 512 = true :=
    PJ3Cn.invB_all (i / 2048) (by change i / 2048 < 13; omega) (i / 512 % 4)
      (by change i / 512 % 4 < 4; omega)
  have h := allBlk_spec h0 (i % 512) (by omega)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (i / 2048) 4) (i / 512 % 4)) 512) (i % 512) = i := by
    change (i / 2048 * 4 + i / 512 % 4) * 512 + i % 512 = i
    omega
  rw [e] at h
  exact invAt_spec tc hH hbs h (cSz ▸ hi) fun hok =>
    nfElt_mem j3ChainArrays (chainCheckFacts PairJ3.chain_check.1) j3Chain_valid.1 hok

theorem xE_mem {i : Nat} (hi : i < 26163) : xE i ∈ P3 := E_mem (inv_rec hi).1

theorem key_rec {i : Nat} (hi : i < 26163) :
    PJ3Cl.K i = keyL 6156 (PJ3Cn.nfp (nfX 4 (PJ3Cl.X i))) PairJ3.bs := by
  have h0 : allBlk (Nat.mul (Nat.add (Nat.mul (i / 512) 8) (i / 64 % 8)) 64)
      (recOKT 6156 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT 4 PairJ3.bs (fun t => rcnt (PJ3.LR t))
        PJ3Cl.X PJ3Cl.K PJ3T.c) 64 = true :=
    PJ3Cl.recB_all (i / 512) (by change i / 512 < 52; omega) (i / 64 % 8)
      (by change i / 64 % 8 < 8; omega)
  have h := allBlk_spec h0 (i % 64) (by omega)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (i / 512) 8) (i / 64 % 8)) 64) (i % 64) = i := by
    change (i / 512 * 8 + i / 64 % 8) * 64 + i % 64 = i
    omega
  rw [e] at h
  unfold recOKT at h
  rw [blt_true (cSz ▸ hi)] at h
  change strictB (nfX 4 (PJ3Cl.X i)) _ = true at h
  rw [strictB_val, bAnd_iff] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem K_inj {i j : Nat} (hi : i < 26163) (hj : j < 26163) (h : PJ3Cl.K i = PJ3Cl.K j) :
    i = j := by
  have srt := keysK_sound (cs := [(PJ3T.c, PJ3Cl.K)]) (by simp) (by decide) PJ3Cl.srtB_all
  have hnd := nodup_of_strictInc_mergeSort srt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hnd
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 (cSz ▸ hi)) (List.mem_range.2 (cSz ▸ hj)) h

theorem xE_inj {i j : Nat} (hi : i < 26163) (hj : j < 26163) (h : xE i = xE j) : i = j := by
  refine K_inj hi hj ?_
  change E (nfX 4 (PJ3Cl.X i)) = E (nfX 4 (PJ3Cl.X j)) at h
  rw [key_rec hi, key_rec hj]
  refine keyL_congr 6156 fun b hb => ?_
  rw [E_rep (inv_rec hi).1 b (hbs b hb), E_rep (inv_rec hj).1 b (hbs b hb), h]

theorem rec_cover {x : P3} (hx : orderOf x = 2) : ∃ i < 26163, xE i = x := by
  let f : Fin 26163 → {x : P3 // orderOf x = 2} := fun i => ⟨mk (xE i) (xE_mem i.2), by
    rw [Subgroup.orderOf_mk]
    exact (inv_rec i.2).2⟩
  have hinj : Function.Injective f := fun i j h => Fin.ext (xE_inj i.2 j.2
    (congrArg (fun g : {x : P3 // orderOf x = 2} => ((g : P3) : Equiv.Perm (Fin 6156))) h))
  obtain ⟨i, hi⟩ := (hinj.bijective_of_nat_card_le (by rw [card_two, Nat.card_fin])).2 ⟨x, hx⟩
  exact ⟨i, i.2, congrArg (fun g : {x : P3 // orderOf x = 2} => ((g : P3) : Equiv.Perm (Fin 6156)))
    hi⟩

def Acond (x w : P3) : Prop :=
  orderOf x = 2 ∧ orderOf (x * w) = 3 ∧ orderOf (w ^ 2 * x * w) = 9

theorem acond_coe (x w : P3) : Acond x w ↔ orderOf x = 2 ∧
    orderOf ((x : Equiv.Perm (Fin 6156)) * w) = 3 ∧
    orderOf ((w : Equiv.Perm (Fin 6156)) ^ 2 * x * w) = 9 := by
  unfold Acond
  rw [← Subgroup.orderOf_coe (x * w), ← Subgroup.orderOf_coe (w ^ 2 * x * w)]
  rfl

theorem scan_count (w : P3) {Z : Nat → Nat} (hZ : RepF 6156 Z w) {V : Nat → Nat}
    (hV : ∀ g < 13, ∀ r < 4, Nat.beq (PJ3Cn.scAt Z (Nat.add (Nat.mul g 4) r))
      (V (Nat.add (Nat.mul g 4) r)) = true) (h57 : sumN 52 V = 57) :
    Nat.card {x : P3 // Acond x w} = 57 := by
  classical
  have hs := chunk_sum 52 512 (scanAt 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT PJ3Cn.bs PJ3T.c PJ3Cl.X Z)
    V fun q hq => by
      have := Nat.eq_of_beq_eq_true (hV (q / 4) (by omega) (q % 4) (Nat.mod_lt _ (by norm_num)))
      rw [split44] at this
      exact this
  rw [h57, sumN_finset] at hs
  have hs2 : ∑ i ∈ Finset.range (52 * 512), (if i < 26163 ∧ orderOf (xE i * w) = 3 ∧
      orderOf ((w : Equiv.Perm (Fin 6156)) ^ 2 * xE i * w) = 9 then 1 else 0) = 57 := by
    rw [← hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hE := scanAt_eq (bs := PJ3Cn.bs) (c := PJ3T.c) (i := i) (X := PJ3Cl.X) tc hH hbs hZ w.2
      (fun hi => (inv_rec (lt_of_lt_of_eq hi cSz)).1)
      (fun hi => xE_mem (lt_of_lt_of_eq hi cSz))
    rw [hE, cSz]
  rw [← Finset.card_filter] at hs2
  rw [← hs2, ← Nat.card_eq_finsetCard]
  symm
  refine Nat.card_eq_of_bijective (fun i => ⟨mk (xE i.1) (xE_mem (Finset.mem_filter.1 i.2).2.1),
    (acond_coe _ _).2 ⟨by rw [Subgroup.orderOf_mk]; exact (inv_rec (Finset.mem_filter.1 i.2).2.1).2,
      (Finset.mem_filter.1 i.2).2.2⟩⟩) ⟨fun i j h => ?_, fun x => ?_⟩
  · have h' := congrArg (fun g : {x : P3 // Acond x w} => ((g : P3) : Equiv.Perm (Fin 6156))) h
    exact Subtype.ext (xE_inj (Finset.mem_filter.1 i.2).2.1 (Finset.mem_filter.1 j.2).2.1 h')
  · have hx := (acond_coe _ _).1 x.2
    obtain ⟨i, hi, he⟩ := rec_cover hx.1
    refine ⟨⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hi, ?_⟩⟩, Subtype.ext
      (Subtype.ext he)⟩
    rw [he]
    exact hx.2

theorem acond_conj (c x w : P3) : Acond (MulAut.conj c x) (MulAut.conj c w) ↔ Acond x w := by
  unfold Acond
  simp only [← map_pow, ← map_mul, MulEquiv.orderOf_eq]

theorem K_val {w : P3} (hw : orderOf w = 19) : Nat.card {x : P3 // Acond x w} = 57 := by
  have hz : Nat.card {x : P3 // Acond x zK} = 57 :=
    scan_count zK (Z := PJ3Cn.zP) (V := PJ3N.SZ) zRep PJ3Cn.scZ_all
      (Nat.eq_of_beq_eq_true PJ3Cn.sZ)
  have hz2 : Nat.card {x : P3 // Acond x (zK ^ 2)} = 57 :=
    scan_count (zK ^ 2) (Z := PJ3Cn.z2P) (V := PJ3N.SZ2)
      ((zRep.comp zRep).congr (by rw [Subgroup.coe_pow, pow_two])) PJ3Cn.scZ2_all
      (Nat.eq_of_beq_eq_true PJ3Cn.sZ2)
  have hc : ∀ v : P3, IsConj v w →
      Nat.card {x : P3 // Acond x w} = Nat.card {x : P3 // Acond x v} := by
    intro v h
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    exact (Nat.card_congr ((MulAut.conj c).toEquiv.subtypeEquiv fun x =>
      (acond_conj c x v).symm)).symm
  rcases ord19_conj hw with h | h
  · rw [hc _ h, hz]
  · rw [hc _ h, hz2]

theorem patRel_iff (x y : P3) : PatRel PairJ3.conds x y ↔
    orderOf (x * y) = 19 ∧ orderOf (x * (y * (x * (y * y)))) = 9 := by
  simp [PatRel, PairJ3.conds, PairJ3.commPat]

theorem card_pairs : Nat.card {p : P3 × P3 // orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧
    PatRel PairJ3.conds p.1 p.2} = 301397760 := by
  classical
  have hxa : ∀ x : P3, orderOf x = 2 → ∀ a, x * (x * a) = a := fun x hx a => by
    rw [← mul_assoc, ← pow_two, ← hx, pow_orderOf_eq_one, one_mul]
  let e : {p : P3 × P3 // orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ PatRel PairJ3.conds p.1 p.2} ≃
      Σ w : {w : P3 // orderOf w = 19}, {x : P3 // Acond x w} :=
    { toFun := fun p => ⟨⟨p.1.1 * p.1.2, ((patRel_iff _ _).1 p.2.2.2).1⟩, ⟨p.1.1, p.2.1, by
          rw [hxa _ p.2.1]; exact p.2.2.1, by
          have := ((patRel_iff _ _).1 p.2.2.2).2
          rwa [show (p.1.1 * p.1.2) ^ 2 * p.1.1 * (p.1.1 * p.1.2) =
            p.1.1 * (p.1.2 * (p.1.1 * (p.1.2 * p.1.2))) by
            simp only [pow_two, mul_assoc, hxa _ p.2.1]]⟩⟩
      invFun := fun q => ⟨(q.2.1, q.2.1 * q.1.1), q.2.2.1, q.2.2.2.1, (patRel_iff _ _).2
        ⟨by rw [hxa _ q.2.2.1]; exact q.1.2, by
          rw [show q.2.1 * (q.2.1 * q.1.1 * (q.2.1 * (q.2.1 * q.1.1 * (q.2.1 * q.1.1)))) =
            q.1.1 ^ 2 * q.2.1 * q.1.1 by simp only [pow_two, mul_assoc, hxa _ q.2.2.1]]
          exact q.2.2.2.2⟩⟩
      left_inv := fun p => by
        apply Subtype.ext
        simp only [hxa _ p.2.1]
      right_inv := fun q => by
        rcases q with ⟨⟨w, hw⟩, ⟨x, hx⟩⟩
        exact Sigma.subtype_ext (Subtype.ext (hxa x hx.1 w)) rfl }
  have : Fintype {w : P3 // orderOf w = 19} := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma]
  rw [Finset.sum_congr rfl fun w _ => K_val w.2, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_nineteen]
  rfl

theorem facts : (PairJ3.parCount (ordPred PairJ3.bs 2) PairJ3.blocks = 26163) ∧
    (PairJ3.parCount (ordPred PairJ3.bs 3) PairJ3.blocks = 253232) ∧
    ((PairJ3.cl.map fun c => c.2.1.size *
      PairJ3.parCount (pairPred PairJ3.bs 3 c.1 PairJ3.conds) PairJ3.blocks).sum = 301397760) := by
  have c2 : PairJ3.parCount (ordPred PairJ3.bs 2) PairJ3.blocks = 26163 := by
    rw [← j3_card_order 2 (by norm_num)]
    exact card_two
  refine ⟨c2, ?_, ?_⟩
  · rw [← j3_card_order 3 (by norm_num)]
    exact card_three
  · obtain ⟨h1', h2, h3, h4⟩ := PairJ3.classes
    have h4' : (PairJ3.cl.map fun c => c.2.1.size).sum =
        countW (fun w => ordB PairJ3.bs w 2) (blocksOf 6156 (rawLevels 6156 j3StrongArrs
          PairJ3.baseArr) PairJ3.groups) [] := by
      rw [h4, ← c2, PairJ3.parCount_eq]
      rfl
    have h := card_pairs_eq_classTotalNF (mx := 2) (my := 3) (conds := PairJ3.conds) j3ChainArrays
      (by norm_num) PairJ3.chain_check.1 j3_bs_eq
      j3_groups (by norm_num) (by norm_num) (by decide) j3_gens PairJ3.cl j3_reps h1' h2 h3 h4'
    rw [card_pairs] at h
    rw [h]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    rw [PairJ3.parCount_eq]
    rfl

end J3

end CertificateChecks.KernelSporSch.PJ3Count

end
