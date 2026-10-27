
module

public import Certificates.Kernel.SporSch.PairHS.CntSmall
public import Certificates.Kernel.SporSch.PairHS.CntSrch
public import Certificates.Kernel.SporSch.PairHS.CntScan
public import Certificates.Kernel.SporSch.PairHS.CntInv
public import Certificates.Kernel.SporSch.PairHS.ClassCard
public import Certificates.Kernel.SporSch.PairHS.Check2219
public import Certificates.Kernel.SporSch.PairJ3.CntGroup
public import CFSG.Certificates.Kernel.SporSch.PairHSCntSound
public import CFSG.Certificates.Kernel.SporSch.ClosNFTClosedProof
public import CFSG.Certificates.Kernel.SporSch.Srch4Proof
public import CFSG.Certificates.Kernel.SporSch.SylowCount
public import CFSG.Sporadic.Schreier.PairHSPairsBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PHSCount

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Certificates
open CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PJ3Group CertificateChecks.KernelSporSch.PHSClass

noncomputable abbrev P3 : Subgroup (Equiv.Perm (Fin 3850)) := hsChain.originalSubgroup

theorem tc : TabChain 3850 12 8 4 PHSC.BP 61 64 PHST.NR PHST.NR 61 1024 4 1024 PHSC.S PHSC.SI
    PHSC.LR PHST.Ts PHST.LT PHST.PT PHST.QT hsStrongArrs PairHS.baseArr PairHS.bs :=
  ⟨PHSCheck.binds, PHSCheck.perm, PHSC.ho, by decide, PHSCheck.tabs, rfl⟩

noncomputable abbrev E (F : Nat) : Equiv.Perm (Fin 3850) :=
  nfElt 3850 hsStrongArrs PairHS.baseArr (nfArr 4 F)

theorem E_rep {F : Nat} (hF : nfValidK 4 PHSC.LR F = true) : RepF 3850 (PHSCn.nfp F) (E F) :=
  (nfPtT_sound tc hF).2

theorem tc' : TabChain 3850 12 8 4 PHSC.BP 61 64 PHST.NR PHST.NR 61 1024 4 1024 PHSC.S PHSC.SI
    PHSC.LR PHST.Ts PHST.LT PHST.PT PHST.QT hsStrongArrs PairHS.baseArr PHSCn.bs := tc

theorem hbs' : ∀ b ∈ PHSCn.bs, b < 3850 := hs_bs_lt

theorem chunk_sum (m B : Nat) (f V : Nat → Nat)
    (h : ∀ q < m, sumN B (fun j => f (Nat.add (Nat.mul q B) j)) = V q) :
    sumN (m * B) f = sumN m V := by
  rw [sumN_mul, sumN_eq, sumN_eq]
  exact congrArg List.sum (List.map_congr_left fun q hq => h q (List.mem_range.1 hq))

theorem split {k q : Nat} : Nat.add (Nat.mul (q / k) k) (q % k) = q := by
  change q / k * k + q % k = q
  exact Nat.div_add_mod' q k

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

theorem blk_spec {R B N : Nat} {f : Nat → Bool} {h : Nat → Nat → Bool}
    (hh : ∀ g r, h g r = allBlk (Nat.mul (Nat.add (Nat.mul g R) r) B) f B)
    (hall : ∀ g < N, ∀ r < R, h g r = true) (hR : 0 < R) (hB : 0 < B) {i : Nat}
    (hi : i < N * R * B) : f i = true := by
  have hg : i / (R * B) < N := by
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos hR hB)]
    rw [Nat.mul_assoc] at hi
    exact hi
  have h0 := hall (i / (R * B)) hg (i / B % R) (Nat.mod_lt _ hR)
  rw [hh] at h0
  have h1 := allBlk_spec h0 (i % B) (Nat.mod_lt _ hB)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (i / (R * B)) R) (i / B % R)) B) (i % B) = i := by
    change (i / (R * B) * R + i / B % R) * B + i % B = i
    have h2 : i / (R * B) * R + i / B % R = i / B := by
      rw [Nat.mul_comm R B, ← Nat.div_div_eq_div_mul]
      exact Nat.div_add_mod' (i / B) R
    rw [h2]
    exact Nat.div_add_mod' i B
  rwa [e] at h1

theorem evR_unpack : ∀ (RP : List Nat), (∀ P ∈ RP, ∀ y < 3850, pg 12 (mask 12) P y < 3850) →
    ∀ x < 3850, evR (RP.map (unpack 3850 12)) x = PHSCn.wordP RP x
  | [], _, x, _ => rfl
  | P :: RP, h, x, hx => by
    rw [List.map_cons, evR_cons, PairGen.unpack_get hx]
    exact evR_unpack RP (fun Q hQ => h Q (List.mem_cons_of_mem P hQ)) _
      (h P List.mem_cons_self x hx)

theorem gen_lt (k : Nat) (hk : k < 8) (y : Nat) (hy : y < 3850) :
    pg 12 (mask 12) (PHSC.S k) y < 3850 := by
  have hI := (invEqK_sound (allN_spec PHSCheck.perm k hk)).2
  have := PairGen.lt_of_isInvA hI hy
  rwa [PairGen.unpack_get hy] at this

section HS

theorem hH : BaseFaithful P3 PairHS.bs := hs_baseFaithful

theorem hH' : BaseFaithful P3 PHSCn.bs := hs_baseFaithful

theorem hbs : ∀ b ∈ PairHS.bs, b < 3850 := hs_bs_lt

theorem E_mem {F : Nat} (hF : nfValidK 4 PHSC.LR F = true) : E F ∈ P3 :=
  nfElt_mem hsChainArrays (chainCheckFacts PairHS.chain_check.1) hsChain_valid.1
    (nfPtT_sound tc hF).1

theorem card_P3 : Nat.card P3 = 44352000 := by
  rw [P3, ← hsP_eq_original]
  exact card_hsP

theorem srch_eq {X Y : Nat → Nat} {x y : Equiv.Perm (Fin 3850)} (hX : RepF 3850 X x)
    (hY : RepF 3850 Y y) (hx : x ∈ P3) (hy : y ∈ P3) (h01 : X 0 = 1) {V : Nat → Nat}
    (hV : ∀ g < 5, ∀ r < 5, Nat.beq (PHSCn.srAt X Y (Nat.add (Nat.mul g 5) r))
      (V (Nat.add (Nat.mul g 5) r)) = true) :
    Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * x = y * g} = sumN 25 V := by
  have h := Tab.srch4_proved (b0 := 0) (b1 := 1) (bs := [2, 3]) hsChainArrays
    PairHS.chain_check.1 (by norm_num) tc hX hY hx hy h01
  rw [← h, Nat.eq_of_beq_eq_true PHSCn.c0]
  refine chunk_sum 25 154 _ V fun q hq => ?_
  have := Nat.eq_of_beq_eq_true (hV (q / 5) (by omega) (q % 5) (Nat.mod_lt _ (by norm_num)))
  rw [split] at this
  exact this

theorem repsF : nfValidK 4 PHSC.LR PHSN.n0 = true ∧ nfValidK 4 PHSC.LR PHSN.n1 = true ∧
    nfValidK 4 PHSC.LR PHSN.n2 = true ∧ nfValidK 4 PHSC.LR PHSN.n3 = true ∧
    nfValidK 4 PHSC.LR PHSN.n4 = true ∧ nfValidK 4 PHSC.LR PHSN.n5 = true ∧
    nfValidK 4 PHSC.LR PHSN.n6 = true ∧ nfValidK 4 PHSC.LR PHSN.n7 = true ∧
    ordPL PHSCn.bs PHSCn.tAP 2 = true ∧ ordPL PHSCn.bs PHSCn.tBP 2 = true ∧
    ordPL PHSCn.bs PHSCn.aP 5 = true ∧ ordPL PHSCn.bs PHSCn.bP 5 = true ∧
    ordPL PHSCn.bs PHSCn.cP 5 = true ∧ ordPL PHSCn.bs PHSCn.zP 11 = true ∧
    Nat.beq (PHSCn.aP 0) 1 = true ∧ Nat.beq (PHSCn.bP 0) 1 = true ∧
    Nat.beq (PHSCn.cP 0) 1 = true ∧ Nat.beq (PHSCn.zP 0) 1 = true ∧
    eqOnL PHSCn.bs (fun b => PHSCn.zP (PHSCn.ziP b)) (fun x => x) = true ∧
    eqOnL PHSCn.bs (fun b => PHSCn.nfp PHSN.n7 (PHSCn.zP b))
      (fun b => powF PHSCn.zP 3 (PHSCn.nfp PHSN.n7 b)) = true := by
  have h := PHSCn.reps
  unfold PHSCn.repsB PHSCn.validB PHSCn.ordsB PHSCn.relsB at h
  simpa only [bAnd_iff, and_assoc] using h

theorem bindAll {g : Nat} (hg : g < 7) {F P : Nat}
    (hFP : ∀ r, PHSCn.bindB g r = PHSCn.bindR F P (Nat.mul r 770)) :
    ∀ x < 3850, bindAt 3850 12 PHST.NR PHST.NR PHST.LT PHST.PT F P x = true := by
  intro x hx
  have h := PHSCn.bindB_all g hg (x / 770) (by change x / 770 < 5; omega)
  rw [hFP] at h
  have h2 := allBlk_spec h (x % 770) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 770) 770) (x % 770) = x := split
  rwa [e] at h2

noncomputable abbrev tAE : Equiv.Perm (Fin 3850) := E PHSN.n0
noncomputable abbrev tBE : Equiv.Perm (Fin 3850) := E PHSN.n1
noncomputable abbrev aE : Equiv.Perm (Fin 3850) := E PHSN.n2
noncomputable abbrev bE : Equiv.Perm (Fin 3850) := E PHSN.n3
noncomputable abbrev cE : Equiv.Perm (Fin 3850) := E PHSN.n4
noncomputable abbrev zE : Equiv.Perm (Fin 3850) := E PHSN.n5
noncomputable abbrev ziE : Equiv.Perm (Fin 3850) := E PHSN.n6
noncomputable abbrev nuE : Equiv.Perm (Fin 3850) := E PHSN.n7

theorem tARep : RepF 3850 PHSCn.tAP tAE :=
  bind_spec tc repsF.1 (bindAll (g := 0) (by norm_num) fun _ => rfl)
theorem tBRep : RepF 3850 PHSCn.tBP tBE :=
  bind_spec tc repsF.2.1 (bindAll (g := 1) (by norm_num) fun _ => rfl)
theorem aRep : RepF 3850 PHSCn.aP aE :=
  bind_spec tc repsF.2.2.1 (bindAll (g := 2) (by norm_num) fun _ => rfl)
theorem bRep : RepF 3850 PHSCn.bP bE :=
  bind_spec tc repsF.2.2.2.1 (bindAll (g := 3) (by norm_num) fun _ => rfl)
theorem cRep : RepF 3850 PHSCn.cP cE :=
  bind_spec tc repsF.2.2.2.2.1 (bindAll (g := 4) (by norm_num) fun _ => rfl)
theorem zRep : RepF 3850 PHSCn.zP zE :=
  bind_spec tc repsF.2.2.2.2.2.1 (bindAll (g := 5) (by norm_num) fun _ => rfl)
theorem ziRep : RepF 3850 PHSCn.ziP ziE :=
  bind_spec tc repsF.2.2.2.2.2.2.1 (bindAll (g := 6) (by norm_num) fun _ => rfl)

theorem tAMem : tAE ∈ P3 := E_mem repsF.1
theorem tBMem : tBE ∈ P3 := E_mem repsF.2.1
theorem aMem : aE ∈ P3 := E_mem repsF.2.2.1
theorem bMem : bE ∈ P3 := E_mem repsF.2.2.2.1
theorem cMem : cE ∈ P3 := E_mem repsF.2.2.2.2.1
theorem zMem : zE ∈ P3 := E_mem repsF.2.2.2.2.2.1
theorem ziMem : ziE ∈ P3 := E_mem repsF.2.2.2.2.2.2.1
theorem nuMem : nuE ∈ P3 := E_mem repsF.2.2.2.2.2.2.2.1

theorem tAOrd : orderOf tAE = 2 :=
  (ordPL_iff hH hbs tARep tAMem Nat.prime_two).1 repsF.2.2.2.2.2.2.2.2.1
theorem tBOrd : orderOf tBE = 2 :=
  (ordPL_iff hH hbs tBRep tBMem Nat.prime_two).1 repsF.2.2.2.2.2.2.2.2.2.1
theorem aOrd : orderOf aE = 5 :=
  (ordPL_iff hH hbs aRep aMem (by norm_num)).1 repsF.2.2.2.2.2.2.2.2.2.2.1
theorem bOrd : orderOf bE = 5 :=
  (ordPL_iff hH hbs bRep bMem (by norm_num)).1 repsF.2.2.2.2.2.2.2.2.2.2.2.1
theorem cOrd : orderOf cE = 5 :=
  (ordPL_iff hH hbs cRep cMem (by norm_num)).1 repsF.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem zOrd : orderOf zE = 11 :=
  (ordPL_iff hH hbs zRep zMem (by norm_num)).1 repsF.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem zziE : zE * ziE = 1 :=
  eq_of_eqOnL hH (zRep.comp ziRep) RepF.one (P3.mul_mem zMem ziMem) P3.one_mem
    repsF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ziE_eq : ziE = zE⁻¹ := eq_inv_of_mul_eq_one_right zziE

theorem nuEq : nuE * zE = zE ^ 3 * nuE :=
  eq_of_eqOnL hH ((E_rep repsF.2.2.2.2.2.2.2.1).comp zRep)
    ((zRep.powF 3).comp (E_rep repsF.2.2.2.2.2.2.2.1)) (P3.mul_mem nuMem zMem)
    (P3.mul_mem (P3.pow_mem zMem 3) nuMem) repsF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem cent_a : Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * aE = aE * g} = 500 := by
  rw [srch_eq aRep aRep aMem aMem (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    PHSCn.srA_all]
  exact Nat.eq_of_beq_eq_true PHSCn.vA

theorem cent_b : Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * bE = bE * g} = 300 := by
  rw [srch_eq bRep bRep bMem bMem (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    PHSCn.srB_all]
  exact Nat.eq_of_beq_eq_true PHSCn.vB

theorem cent_c : Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * cE = cE * g} = 25 := by
  rw [srch_eq cRep cRep cMem cMem
    (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) PHSCn.srC_all]
  exact Nat.eq_of_beq_eq_true PHSCn.vC

theorem cent_z : Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * zE = zE * g} = 11 := by
  rw [srch_eq zRep zRep zMem zMem
    (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) PHSCn.srZ_all]
  exact Nat.eq_of_beq_eq_true PHSCn.vZ

theorem cent_zi : Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * zE = ziE * g} = 0 := by
  rw [srch_eq zRep ziRep zMem ziMem
    (Nat.eq_of_beq_eq_true repsF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) PHSCn.srZI_all]
  exact Nat.eq_of_beq_eq_true PHSCn.vZI

abbrev mk (x : Equiv.Perm (Fin 3850)) (hx : x ∈ P3) : P3 := ⟨x, hx⟩

theorem cent_K (x : P3) {N : Nat}
    (h : Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * x = x * g} = N) :
    Nat.card {g : P3 // g * x = x * g} = N := by
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => Subtype.ext_iff)

theorem card_class (x : P3) {N : Nat}
    (h : Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * x = x * g} = N) (hN : 0 < N) :
    Nat.card {y : P3 // IsConj x y} = 44352000 / N := by
  have h2 := card_class_mul x
  rw [cent_K x h, card_P3] at h2
  rw [← h2, Nat.mul_div_cancel _ hN]

theorem orderOf_conj (c x : P3) : orderOf (c * x * c⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem orderOf_of_isConj {x y : P3} (h : IsConj x y) : orderOf y = orderOf x := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact orderOf_conj c x

theorem isConj_of_eq {d y r : P3} (h : d * y = r * d) : IsConj y r :=
  isConj_iff.2 ⟨d, by rw [h, mul_inv_cancel_right]⟩

theorem not_conj_of_card {x y : P3} {N M : Nat} (hx : Nat.card {u : P3 // IsConj x u} = N)
    (hy : Nat.card {u : P3 // IsConj y u} = M) (hNM : N ≠ M) : ¬IsConj x y := by
  intro h
  have e : {u : P3 // IsConj x u} ≃ {u : P3 // IsConj y u} :=
    Equiv.subtypeEquivRight fun u => ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩
  rw [Nat.card_congr e, hy] at hx
  exact hNM hx.symm

theorem fact2 : (Nat.card P3).factorization 2 = 9 :=
  factorization_eq Nat.prime_two (m := 86625) (by norm_num) (by rw [card_P3]; norm_num)

theorem fact5 : (Nat.card P3).factorization 5 = 3 :=
  factorization_eq (by norm_num) (m := 354816) (by norm_num) (by rw [card_P3]; norm_num)

theorem fact11 : (Nat.card P3).factorization 11 = 1 :=
  factorization_eq (by norm_num) (m := 4032000) (by norm_num) (by rw [card_P3]; norm_num)

noncomputable abbrev EA : Array (Array Nat) × Array Nat × Array Nat := PairHS.closureOf PairHS.wA

noncomputable abbrev EB : Array (Array Nat) × Array Nat × Array Nat := PairHS.closureOf PairHS.wC

theorem hgen : P3 ≤ Subgroup.closure {g | ∃ l < PairHS.gens.size, hsGen l = g} := by
  rw [P3, ← hsP_eq_original, hsP]
  refine Subgroup.closure_mono ?_
  rintro g (rfl | rfl)
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩

theorem closedA : ∀ i < EA.1.size, ∀ l < PairHS.gens.size, ∃ j < EA.1.size,
    baseImgs PairHS.bs (nfWord (rawLevels 3850 hsStrongArrs PairHS.baseArr) EA.1[j]!) =
      conjImgs PairHS.bs PairHS.gens[l]! PairHS.gensInv[l]!
        (nfWord (rawLevels 3850 hsStrongArrs PairHS.baseArr) EA.1[i]!) :=
  ClTP.closNFT_closedP (bs := PairHS.bs) (rep := PairHS.wA) PHSCheck.binds PHSCheck.perm PHSC.ho
    (by decide) PHSCheck.tabs rfl PHSCheck.hg PHSCheck.repA_eq PHSCheck.okA

theorem closedB : ∀ i < EB.1.size, ∀ l < PairHS.gens.size, ∃ j < EB.1.size,
    baseImgs PairHS.bs (nfWord (rawLevels 3850 hsStrongArrs PairHS.baseArr) EB.1[j]!) =
      conjImgs PairHS.bs PairHS.gens[l]! PairHS.gensInv[l]!
        (nfWord (rawLevels 3850 hsStrongArrs PairHS.baseArr) EB.1[i]!) :=
  ClTP.closNFT_closedP (bs := PairHS.bs) (rep := PairHS.wC) PHSCheck.binds PHSCheck.perm PHSC.ho
    (by decide) PHSCheck.tabs rfl PHSCheck.hg PHSCheck.repB_eq PHSCheck.okB

theorem sizeA : EA.1.size = 5775 :=
  (ClTP.closNFT_proved (bs := PairHS.bs) (rep := PairHS.wA) PHSCheck.binds PHSCheck.perm PHSC.ho
    (by decide) PHSCheck.tabs rfl PHSCheck.hg PHSCheck.repA_eq PHSCheck.okA).2.1.trans
    (Nat.eq_of_beq_eq_true PHSCl.cASz)

theorem sizeB : EB.1.size = 15400 :=
  (ClTP.closNFT_proved (bs := PairHS.bs) (rep := PairHS.wC) PHSCheck.binds PHSCheck.perm PHSC.ho
    (by decide) PHSCheck.tabs rfl PHSCheck.hg PHSCheck.repB_eq PHSCheck.okB).2.1.trans
    (Nat.eq_of_beq_eq_true PHSCl.cBSz)

theorem okA : closureOK (rawLevels 3850 hsStrongArrs PairHS.baseArr) PairHS.bs PairHS.gens
    PairHS.gensInv PairHS.wA EA.1 EA.2.1 EA.2.2 = true :=
  PairHS.classes.2.1 (PairHS.wA, EA) (by simp [PairHS.cl])

theorem okB : closureOK (rawLevels 3850 hsStrongArrs PairHS.baseArr) PairHS.bs PairHS.gens
    PairHS.gensInv PairHS.wC EB.1 EB.2.1 EB.2.2 = true :=
  PairHS.classes.2.1 (PairHS.wC, EB) (by simp [PairHS.cl])

noncomputable abbrev keysOf (E : Array (Array Nat)) : List Nat :=
  E.toList.map fun nf => imgKey 3850 (baseImgs PairHS.bs
    (nfWord (rawLevels 3850 hsStrongArrs PairHS.baseArr) nf))

theorem keys_nodup :(keysOf EA.1 ++ keysOf EB.1).Nodup := by
  have h := PairHS.classes.2.2.1
  unfold keysDistinctNF at h
  have hn := CFSG.KS.SporSch.nodup_of_strictInc_mergeSort h
  simp only [PairHS.cl, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at hn
  exact hn

theorem words {x : Nat} (hx : x < 3850) : PHSCn.tAP x = PHSCn.wordP PHSCl.RPA x ∧
    PHSCn.tBP x = PHSCn.wordP PHSCl.RPB x := by
  have h := PHSCn.WB.all (x / 770) (by change x / 770 < 5; omega)
  unfold PHSCn.wordB at h
  have h2 := allBlk_spec h (x % 770) (Nat.mod_lt _ (by norm_num))
  rw [split] at h2
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  exact ⟨Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem rp_lt {RP : List Nat} (h : ∀ P ∈ RP, P = PHSC.S 0 ∨ P = PHSC.S 1) :
    ∀ P ∈ RP, ∀ y < 3850, pg 12 (mask 12) P y < 3850 := by
  intro P hP y hy
  rcases h P hP with rfl | rfl
  · exact gen_lt 0 (by norm_num) y hy
  · exact gen_lt 1 (by norm_num) y hy

theorem repWA : RepW 3850 PairHS.wA tAE := by
  intro x
  rw [PHSCheck.repA_eq, evR_unpack _ (rp_lt fun P hP => by
    simp only [PHSCl.RPA, List.mem_singleton] at hP
    exact Or.inl hP) x x.2, ← (words x.2).1]
  exact tARep x x.2

theorem repWB : RepW 3850 PairHS.wC tBE := by
  intro x
  rw [PHSCheck.repB_eq, evR_unpack _ (rp_lt fun P hP => by
    simp only [PHSCl.RPB, List.mem_cons, List.not_mem_nil, or_false] at hP
    tauto) x x.2,
    ← (words x.2).2]
  exact tBRep x x.2

theorem card_clA : Nat.card {y : P3 // IsConj (mk tAE tAMem) y} = 5775 := by
  rw [card_class_of_closed hsChainArrays (chainCheckFacts PairHS.chain_check.1) hsChain_valid.1
    hH hbs hs_gens hgen repWA tAMem okA closedA (List.nodup_append.1 keys_nodup).1, sizeA]

theorem card_clB : Nat.card {y : P3 // IsConj (mk tBE tBMem) y} = 15400 := by
  rw [card_class_of_closed hsChainArrays (chainCheckFacts PairHS.chain_check.1) hsChain_valid.1
    hH hbs hs_gens hgen repWB tBMem okB closedB (List.nodup_append.1 keys_nodup).2.1, sizeB]

noncomputable abbrev tAK : P3 := mk tAE tAMem
noncomputable abbrev tBK : P3 := mk tBE tBMem

theorem not_conj_AB : ¬IsConj tAK tBK := not_conj_of_card card_clA card_clB (by norm_num)

theorem s2_row {i : Nat} (hi : i < 512) : PHSCn.s2At i = true :=
  blk_spec (R := 8) (B := 8) (N := 8) (h := PHSCn.s2B) (fun _ _ => rfl) PHSCn.s2B_all
    (by norm_num) (by norm_num) (by norm_num; exact hi)

theorem s2_parts {i : Nat} (hi : i < 512) :
    nfValidK 4 PHSC.LR (PHSCn.r2 i) = true ∧
    (0 < i → PHSCn.par2 i < i ∧ PHSCn.lab2 i < 3 ∧ eqOnL PHSCn.bs (PHSCn.nfp (PHSCn.r2 i))
      (fun b => PHSCn.nfp (PHSCn.r2 (PHSCn.par2 i))
        (PHSCn.nfp (PHSCn.r2 (PHSCn.gr2 (PHSCn.lab2 i))) b)) = true) ∧
    (i = 0 → eqOnL PHSCn.bs (PHSCn.nfp (PHSCn.r2 i)) (fun x => x) = true) ∧
    (∀ l < 3, PHSCn.m2 i l < 512 ∧ eqOnL PHSCn.bs
      (fun b => PHSCn.nfp (PHSCn.r2 i) (PHSCn.nfp (PHSCn.r2 (PHSCn.gr2 l)) b))
      (PHSCn.nfp (PHSCn.r2 (PHSCn.m2 i l))) = true) ∧
    (ordPL PHSCn.bs (PHSCn.nfp (PHSCn.r2 i)) 2 = true → nfValidK 4 PHSC.LR (PHSCn.d2 i) = true ∧
      eqOnL PHSCn.bs (fun b => PHSCn.nfp (PHSCn.d2 i) (PHSCn.tSel (PHSCn.c2 i) b))
        (fun b => PHSCn.nfp (PHSCn.r2 i) (PHSCn.nfp (PHSCn.d2 i) b)) = true) := by
  have h := s2_row hi
  unfold PHSCn.s2At at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun hp => ?_, fun h0 => ?_, fun l hl => ?_, fun ho => ?_⟩
  · rw [blt_true hp, bAnd_iff, bAnd_iff] at h2
    exact ⟨Nat.blt_eq.mp h2.1, Nat.blt_eq.mp h2.2.1, h2.2.2⟩
  · subst h0
    exact h2
  · have := allN_spec h3 l hl
    rw [bAnd_iff] at this
    exact ⟨Nat.blt_eq.mp this.1, this.2⟩
  · rw [ho, bAnd_iff] at h4
    exact h4

noncomputable abbrev r2E (i : Nat) : Equiv.Perm (Fin 3850) := E (PHSCn.r2 i)

theorem r2_mem {i : Nat} (hi : i < 512) : r2E i ∈ P3 := E_mem (s2_parts hi).1

theorem gr2_lt {l : Nat} (hl : l < 3) : PHSCn.gr2 l < 512 := by
  have h := PHSCn.gens
  unfold PHSCn.gensB at h
  rw [bAnd_iff] at h
  exact Nat.blt_eq.mp (allN_spec h.1 l hl)

theorem r2_one : r2E 0 = 1 :=
  eq_of_eqOnL hH (E_rep (s2_parts (by norm_num)).1) RepF.one (r2_mem (by norm_num)) P3.one_mem
    ((s2_parts (by norm_num)).2.2.1 rfl)

theorem r2_tree {i : Nat} (hi : i < 512) (hp : 0 < i) :
    PHSCn.par2 i < i ∧ PHSCn.lab2 i < 3 ∧
      r2E i = r2E (PHSCn.par2 i) * r2E (PHSCn.gr2 (PHSCn.lab2 i)) := by
  obtain ⟨h1, h2, h3⟩ := (s2_parts hi).2.1 hp
  have hq := gr2_lt h2
  exact ⟨h1, h2, eq_of_eqOnL hH (E_rep (s2_parts hi).1)
    ((E_rep (s2_parts (h1.trans hi)).1).comp (E_rep (s2_parts hq).1)) (r2_mem hi)
    (P3.mul_mem (r2_mem (h1.trans hi)) (r2_mem hq)) h3⟩

theorem r2_mul {i l : Nat} (hi : i < 512) (hl : l < 3) :
    PHSCn.m2 i l < 512 ∧ r2E i * r2E (PHSCn.gr2 l) = r2E (PHSCn.m2 i l) := by
  obtain ⟨hm, he⟩ := (s2_parts hi).2.2.2.1 l hl
  have hq := gr2_lt hl
  exact ⟨hm, eq_of_eqOnL hH ((E_rep (s2_parts hi).1).comp (E_rep (s2_parts hq).1))
    (E_rep (s2_parts hm).1) (P3.mul_mem (r2_mem hi) (r2_mem hq)) (r2_mem hm) he⟩

theorem K2_inj {i j : Nat} (hi : i < 512) (hj : j < 512) (h : PHSCn.K2 i = PHSCn.K2 j) :
    i = j := by
  have srt := keysK_sound (cs := [(512, PHSCn.K2)]) (nB := 8) (R := 8) (B := 8) (by simp)
    (by decide) PHSCn.srt2_all
  have hnd := nodup_of_strictInc_mergeSort srt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hnd
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 hi) (List.mem_range.2 hj) h

theorem r2_inj {i j : Nat} (hi : i < 512) (hj : j < 512) (h : r2E i = r2E j) : i = j := by
  refine K2_inj hi hj ?_
  unfold PHSCn.K2
  refine keyL_congr 3850 fun b hb => ?_
  have h' : E (PHSCn.r2 i) = E (PHSCn.r2 j) := h
  rw [E_rep (s2_parts hi).1 b (hbs' b hb), E_rep (s2_parts hj).1 b (hbs' b hb), h']

def s2Set : Set P3 := {g | ∃ i < 512, (g : Equiv.Perm (Fin 3850)) = r2E i}

theorem s2_closed : ∀ a ∈ s2Set, ∀ b ∈ s2Set, a * b ∈ s2Set := by
  rintro a ⟨i, hi, ha⟩ b ⟨j, hj, hb⟩
  obtain ⟨t, ht, hte⟩ := mul_mem_of_table (N := 512) (k := 3) (r := r2E) (gi := PHSCn.gr2)
    (par := PHSCn.par2) (lab := PHSCn.lab2) (m := PHSCn.m2) r2_one (fun i hi hp => r2_tree hi hp)
    (fun i hi l hl => r2_mul hi hl) j hj i hi
  exact ⟨t, ht, by rw [Subgroup.coe_mul, ha, hb, hte]⟩

noncomputable def S2 : Subgroup P3 :=
  mulClosed s2Set s2_closed (mk (r2E 0) (r2_mem (by norm_num))) ⟨0, by norm_num, rfl⟩

theorem card_S2 : Nat.card S2 = 512 := by
  have hb : Function.Bijective (fun i : Fin 512 =>
      (⟨mk (r2E i) (r2_mem i.2), mem_mulClosed.2 ⟨i, i.2, rfl⟩⟩ : S2)) := by
    refine ⟨fun i j h => Fin.ext (r2_inj i.2 j.2 ?_), fun g => ?_⟩
    · have := congrArg (fun g : S2 => ((g : P3) : Equiv.Perm (Fin 3850))) h
      exact this
    · obtain ⟨i, hi, he⟩ := mem_mulClosed.1 g.2
      exact ⟨⟨i, hi⟩, Subtype.ext (Subtype.ext he.symm)⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_fin]

theorem tSel_rep (c : Nat) : RepF 3850 (PHSCn.tSel c) (if c = 0 then tAE else tBE) := by
  intro x hx
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left rfl]
    exact tARep x hx
  · rw [ite_eq_right hc]
    have : Nat.beq c 0 = false := by
      cases h : Nat.beq c 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hc
    change Bool.rec (motive := fun _ => Nat) (PHSCn.tBP x) (PHSCn.tAP x) (Nat.beq c 0) = _
    rw [this]
    exact tBRep x hx

theorem invol_conj {x : P3} (hx : orderOf x = 2) : IsConj tAK x ∨ IsConj tBK x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_conj_mem S2 (by rw [card_S2, fact2]; norm_num) (k := 1)
    (by rw [hx, pow_one])
  obtain ⟨i, hi, he⟩ := mem_mulClosed.1 hg
  have ho : orderOf (r2E i) = 2 := by
    rw [← he, Subgroup.orderOf_coe, orderOf_conj, hx]
  obtain ⟨hd, heq⟩ := (s2_parts hi).2.2.2.2
    ((ordPL_iff hH hbs (E_rep (s2_parts hi).1) (r2_mem hi) Nat.prime_two).2 ho)
  have hD := E_mem hd
  have hT : (if PHSCn.c2 i = 0 then tAE else tBE) ∈ P3 := by
    split
    · exact tAMem
    · exact tBMem
  have h1 := eq_of_eqOnL hH ((E_rep hd).comp (tSel_rep (PHSCn.c2 i)))
    ((E_rep (s2_parts hi).1).comp (E_rep hd)) (P3.mul_mem hD hT) (P3.mul_mem (r2_mem hi) hD) heq
  have hb : IsConj (g * x * g⁻¹) x := isConj_iff.2 ⟨g⁻¹, by group⟩
  by_cases hc : PHSCn.c2 i = 0
  · rw [ite_eq_left hc] at h1
    refine Or.inl ((isConj_of_eq (d := mk _ hD) (r := g * x * g⁻¹) (Subtype.ext ?_)).trans hb)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, he]
    exact h1
  · rw [ite_eq_right hc] at h1
    refine Or.inr ((isConj_of_eq (d := mk _ hD) (r := g * x * g⁻¹) (Subtype.ext ?_)).trans hb)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, he]
    exact h1

theorem card_two : Nat.card {x : P3 // orderOf x = 2} = 21175 := by
  have e : {x : P3 // orderOf x = 2} ≃ {y : P3 // IsConj tAK y ∨ IsConj tBK y} :=
    Equiv.subtypeEquivRight fun x => ⟨invol_conj, fun h => by
      rcases h with h | h
      · rw [orderOf_of_isConj h, Subgroup.orderOf_mk]
        exact tAOrd
      · rw [orderOf_of_isConj h, Subgroup.orderOf_mk]
        exact tBOrd⟩
  have hd : Disjoint (fun y : P3 => IsConj tAK y) (fun y => IsConj tBK y) := by
    rw [Pi.disjoint_iff]
    intro y
    rw [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩
    exact not_conj_AB (h1.trans h2.symm)
  classical
  rw [Nat.card_congr (e.trans (subtypeOrEquiv _ _ hd)), Nat.card_sum, card_clA, card_clB]

theorem s5_row {i : Nat} (hi : i < 125) : PHSCn.s5At i = true :=
  blk_spec (R := 5) (B := 5) (N := 5) (h := PHSCn.s5B) (fun _ _ => rfl) PHSCn.s5B_all
    (by norm_num) (by norm_num) (by norm_num; exact hi)

theorem s5_parts {i : Nat} (hi : i < 125) :
    nfValidK 4 PHSC.LR (PHSCn.r5 i) = true ∧
    (0 < i → PHSCn.par5 i < i ∧ PHSCn.lab5 i < 2 ∧ eqOnL PHSCn.bs (PHSCn.nfp (PHSCn.r5 i))
      (fun b => PHSCn.nfp (PHSCn.r5 (PHSCn.par5 i))
        (PHSCn.nfp (PHSCn.r5 (PHSCn.gr5 (PHSCn.lab5 i))) b)) = true) ∧
    (i = 0 → eqOnL PHSCn.bs (PHSCn.nfp (PHSCn.r5 i)) (fun x => x) = true) ∧
    (∀ l < 2, PHSCn.m5 i l < 125 ∧ eqOnL PHSCn.bs
      (fun b => PHSCn.nfp (PHSCn.r5 i) (PHSCn.nfp (PHSCn.r5 (PHSCn.gr5 l)) b))
      (PHSCn.nfp (PHSCn.r5 (PHSCn.m5 i l))) = true) ∧
    (ordPL PHSCn.bs (PHSCn.nfp (PHSCn.r5 i)) 5 = true → nfValidK 4 PHSC.LR (PHSCn.d5 i) = true ∧
      PHSCn.c5 i < 3 ∧
      eqOnL PHSCn.bs (fun b => PHSCn.nfp (PHSCn.d5 i) (PHSCn.ySel (PHSCn.c5 i) b))
        (fun b => PHSCn.nfp (PHSCn.r5 i) (PHSCn.nfp (PHSCn.d5 i) b)) = true) := by
  have h := s5_row hi
  unfold PHSCn.s5At at h
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun hp => ?_, fun h0 => ?_, fun l hl => ?_, fun ho => ?_⟩
  · rw [blt_true hp, bAnd_iff, bAnd_iff] at h2
    exact ⟨Nat.blt_eq.mp h2.1, Nat.blt_eq.mp h2.2.1, h2.2.2⟩
  · subst h0
    exact h2
  · have := allN_spec h3 l hl
    rw [bAnd_iff] at this
    exact ⟨Nat.blt_eq.mp this.1, this.2⟩
  · rw [ho, bAnd_iff, bAnd_iff] at h4
    exact ⟨h4.1, Nat.blt_eq.mp h4.2.1, h4.2.2⟩

noncomputable abbrev r5E (i : Nat) : Equiv.Perm (Fin 3850) := E (PHSCn.r5 i)

theorem r5_mem {i : Nat} (hi : i < 125) : r5E i ∈ P3 := E_mem (s5_parts hi).1

theorem gr5_lt {l : Nat} (hl : l < 2) : PHSCn.gr5 l < 125 := by
  have h := PHSCn.gens
  unfold PHSCn.gensB at h
  rw [bAnd_iff] at h
  exact Nat.blt_eq.mp (allN_spec h.2 l hl)

theorem r5_one : r5E 0 = 1 :=
  eq_of_eqOnL hH (E_rep (s5_parts (by norm_num)).1) RepF.one (r5_mem (by norm_num)) P3.one_mem
    ((s5_parts (by norm_num)).2.2.1 rfl)

theorem r5_tree {i : Nat} (hi : i < 125) (hp : 0 < i) :
    PHSCn.par5 i < i ∧ PHSCn.lab5 i < 2 ∧
      r5E i = r5E (PHSCn.par5 i) * r5E (PHSCn.gr5 (PHSCn.lab5 i)) := by
  obtain ⟨h1, h2, h3⟩ := (s5_parts hi).2.1 hp
  have hq := gr5_lt h2
  exact ⟨h1, h2, eq_of_eqOnL hH (E_rep (s5_parts hi).1)
    ((E_rep (s5_parts (h1.trans hi)).1).comp (E_rep (s5_parts hq).1)) (r5_mem hi)
    (P3.mul_mem (r5_mem (h1.trans hi)) (r5_mem hq)) h3⟩

theorem r5_mul {i l : Nat} (hi : i < 125) (hl : l < 2) :
    PHSCn.m5 i l < 125 ∧ r5E i * r5E (PHSCn.gr5 l) = r5E (PHSCn.m5 i l) := by
  obtain ⟨hm, he⟩ := (s5_parts hi).2.2.2.1 l hl
  have hq := gr5_lt hl
  exact ⟨hm, eq_of_eqOnL hH ((E_rep (s5_parts hi).1).comp (E_rep (s5_parts hq).1))
    (E_rep (s5_parts hm).1) (P3.mul_mem (r5_mem hi) (r5_mem hq)) (r5_mem hm) he⟩

theorem K5_inj {i j : Nat} (hi : i < 125) (hj : j < 125) (h : PHSCn.K5 i = PHSCn.K5 j) :
    i = j := by
  have srt := keysK_sound (cs := [(125, PHSCn.K5)]) (nB := 5) (R := 5) (B := 5) (by simp)
    (by decide) PHSCn.srt5_all
  have hnd := nodup_of_strictInc_mergeSort srt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hnd
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 hi) (List.mem_range.2 hj) h

theorem r5_inj {i j : Nat} (hi : i < 125) (hj : j < 125) (h : r5E i = r5E j) : i = j := by
  refine K5_inj hi hj ?_
  unfold PHSCn.K5
  refine keyL_congr 3850 fun b hb => ?_
  have h' : E (PHSCn.r5 i) = E (PHSCn.r5 j) := h
  rw [E_rep (s5_parts hi).1 b (hbs' b hb), E_rep (s5_parts hj).1 b (hbs' b hb), h']

def s5Set : Set P3 := {g | ∃ i < 125, (g : Equiv.Perm (Fin 3850)) = r5E i}

theorem s5_closed : ∀ a ∈ s5Set, ∀ b ∈ s5Set, a * b ∈ s5Set := by
  rintro a ⟨i, hi, ha⟩ b ⟨j, hj, hb⟩
  obtain ⟨t, ht, hte⟩ := mul_mem_of_table (N := 125) (k := 2) (r := r5E) (gi := PHSCn.gr5)
    (par := PHSCn.par5) (lab := PHSCn.lab5) (m := PHSCn.m5) r5_one (fun i hi hp => r5_tree hi hp)
    (fun i hi l hl => r5_mul hi hl) j hj i hi
  exact ⟨t, ht, by rw [Subgroup.coe_mul, ha, hb, hte]⟩

noncomputable def S5 : Subgroup P3 :=
  mulClosed s5Set s5_closed (mk (r5E 0) (r5_mem (by norm_num))) ⟨0, by norm_num, rfl⟩

theorem card_S5 : Nat.card S5 = 125 := by
  have hb : Function.Bijective (fun i : Fin 125 =>
      (⟨mk (r5E i) (r5_mem i.2), mem_mulClosed.2 ⟨i, i.2, rfl⟩⟩ : S5)) := by
    refine ⟨fun i j h => Fin.ext (r5_inj i.2 j.2 ?_), fun g => ?_⟩
    · have := congrArg (fun g : S5 => ((g : P3) : Equiv.Perm (Fin 3850))) h
      exact this
    · obtain ⟨i, hi, he⟩ := mem_mulClosed.1 g.2
      exact ⟨⟨i, hi⟩, Subtype.ext (Subtype.ext he.symm)⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_fin]

noncomputable abbrev aK : P3 := mk aE aMem
noncomputable abbrev bK : P3 := mk bE bMem
noncomputable abbrev cK : P3 := mk cE cMem

theorem ySel_rep (c : Nat) :
    RepF 3850 (PHSCn.ySel c) (if c = 0 then aE else if c = 1 then bE else cE) := by
  intro x hx
  by_cases hc0 : c = 0
  · subst hc0
    exact aRep x hx
  · have h0 : Nat.beq c 0 = false := by
      cases h : Nat.beq c 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hc0
    rw [ite_eq_right hc0]
    by_cases hc1 : c = 1
    · subst hc1
      exact bRep x hx
    · have h1 : Nat.beq c 1 = false := by
        cases h : Nat.beq c 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hc1
      rw [ite_eq_right hc1]
      change Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (PHSCn.cP x) (PHSCn.bP x) (Nat.beq c 1)) (PHSCn.aP x)
        (Nat.beq c 0) = _
      rw [h0, h1]
      exact cRep x hx

theorem ord5_conj {x : P3} (hx : orderOf x = 5) : IsConj aK x ∨ IsConj bK x ∨ IsConj cK x := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_conj_mem S5 (by rw [card_S5, fact5]; norm_num) (k := 1)
    (by rw [hx, pow_one])
  obtain ⟨i, hi, he⟩ := mem_mulClosed.1 hg
  have ho : orderOf (r5E i) = 5 := by
    rw [← he, Subgroup.orderOf_coe, orderOf_conj, hx]
  obtain ⟨hd, hc3, heq⟩ := (s5_parts hi).2.2.2.2
    ((ordPL_iff hH hbs (E_rep (s5_parts hi).1) (r5_mem hi) (by norm_num)).2 ho)
  have hD := E_mem hd
  have hY : (if PHSCn.c5 i = 0 then aE else if PHSCn.c5 i = 1 then bE else cE) ∈ P3 := by
    split
    · exact aMem
    · split
      · exact bMem
      · exact cMem
  have h1 := eq_of_eqOnL hH ((E_rep hd).comp (ySel_rep (PHSCn.c5 i)))
    ((E_rep (s5_parts hi).1).comp (E_rep hd)) (P3.mul_mem hD hY) (P3.mul_mem (r5_mem hi) hD) heq
  have hb : IsConj (g * x * g⁻¹) x := isConj_iff.2 ⟨g⁻¹, by group⟩
  have key : ∀ {Y : Equiv.Perm (Fin 3850)} (hYm : Y ∈ P3),
      E (PHSCn.d5 i) * Y = r5E i * E (PHSCn.d5 i) → IsConj (mk Y hYm) x := fun hYm h1 =>
    (isConj_of_eq (d := mk _ hD) (r := g * x * g⁻¹) (Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, he]
      exact h1))).trans hb
  by_cases hc0 : PHSCn.c5 i = 0
  · rw [ite_eq_left hc0] at h1
    exact Or.inl (key aMem h1)
  · rw [ite_eq_right hc0] at h1
    by_cases hc1 : PHSCn.c5 i = 1
    · rw [ite_eq_left hc1] at h1
      exact Or.inr (Or.inl (key bMem h1))
    · rw [ite_eq_right hc1] at h1
      exact Or.inr (Or.inr (key cMem h1))

theorem card_clA5 : Nat.card {y : P3 // IsConj aK y} = 88704 := card_class aK cent_a (by norm_num)
theorem card_clB5 : Nat.card {y : P3 // IsConj bK y} = 147840 := card_class bK cent_b (by norm_num)
theorem card_clC5 : Nat.card {y : P3 // IsConj cK y} = 1774080 :=
  card_class cK cent_c (by norm_num)

theorem card_five : Nat.card {x : P3 // orderOf x = 5} = 2010624 := by
  have e : {x : P3 // orderOf x = 5} ≃ {y : P3 // IsConj aK y ∨ (IsConj bK y ∨ IsConj cK y)} :=
    Equiv.subtypeEquivRight fun x => ⟨ord5_conj, fun h => by
      rcases h with h | h | h
      · rw [orderOf_of_isConj h, Subgroup.orderOf_mk]
        exact aOrd
      · rw [orderOf_of_isConj h, Subgroup.orderOf_mk]
        exact bOrd
      · rw [orderOf_of_isConj h, Subgroup.orderOf_mk]
        exact cOrd⟩
  have nab := not_conj_of_card card_clA5 card_clB5 (by norm_num)
  have nac := not_conj_of_card card_clA5 card_clC5 (by norm_num)
  have nbc := not_conj_of_card card_clB5 card_clC5 (by norm_num)
  have hd1 : Disjoint (fun y : P3 => IsConj bK y) (fun y => IsConj cK y) := by
    rw [Pi.disjoint_iff]
    intro y
    rw [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩
    exact nbc (h1.trans h2.symm)
  have hd : Disjoint (fun y : P3 => IsConj aK y) (fun y => IsConj bK y ∨ IsConj cK y) := by
    rw [Pi.disjoint_iff]
    intro y
    rw [Prop.disjoint_iff]
    rintro ⟨h1, h2 | h2⟩
    · exact nab (h1.trans h2.symm)
    · exact nac (h1.trans h2.symm)
  classical
  rw [Nat.card_congr (e.trans (subtypeOrEquiv _ _ hd)), Nat.card_sum,
    Nat.card_congr (subtypeOrEquiv _ _ hd1), Nat.card_sum, card_clA5, card_clB5, card_clC5]

noncomputable abbrev zK : P3 := mk zE zMem
noncomputable abbrev nuK : P3 := mk nuE nuMem

theorem zK_ord : orderOf zK = 11 := by
  rw [Subgroup.orderOf_mk]
  exact zOrd

theorem nuK_eq : nuK * zK * nuK⁻¹ = zK ^ 3 := by
  have h : nuK * zK = zK ^ 3 * nuK := Subtype.ext nuEq
  rw [h, mul_inv_cancel_right]

theorem ord11_conj {x : P3} (hx : orderOf x = 11) : IsConj zK x ∨ IsConj zK⁻¹ x := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hdvd : ¬11 ^ 2 ∣ Nat.card P3 := by
    rw [card_P3]
    norm_num
  exact CFSG.KS.SylowCount.cover_eleven zK_ord nuK_eq
    (CFSG.KS.SylowCount.conj_pow_of_orderOf hdvd zK_ord hx) hx

theorem not_conj_z : ¬IsConj zK zK⁻¹ := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hc' : (c : Equiv.Perm (Fin 3850)) * zE = ziE * c := by
    have : c * zK = zK⁻¹ * c := by rw [← hc, inv_mul_cancel_right]
    have := congrArg Subtype.val this
    rw [ziE_eq]
    exact this
  have hne : Nonempty {g : P3 // (g : Equiv.Perm (Fin 3850)) * zE = ziE * g} := ⟨⟨c, hc'⟩⟩
  have := Nat.card_pos (α := {g : P3 // (g : Equiv.Perm (Fin 3850)) * zE = ziE * g})
  rw [cent_zi] at this
  exact absurd this (lt_irrefl 0)

theorem cent_zinv : Nat.card {g : P3 // (g : Equiv.Perm (Fin 3850)) * (zK⁻¹ : P3) =
    (zK⁻¹ : P3) * g} = 11 := by
  rw [← cent_K zK cent_z]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, Subtype.val_inj]
  change Commute g zK⁻¹ ↔ Commute g zK
  exact Commute.inv_right_iff

theorem card_clz : Nat.card {y : P3 // IsConj zK y} = 4032000 := card_class zK cent_z (by norm_num)

theorem card_clzi : Nat.card {y : P3 // IsConj zK⁻¹ y} = 4032000 :=
  card_class zK⁻¹ cent_zinv (by norm_num)

theorem card_eleven : Nat.card {x : P3 // orderOf x = 11} = 8064000 := by
  have hzi : orderOf zK⁻¹ = 11 := by rw [orderOf_inv, zK_ord]
  have e : {x : P3 // orderOf x = 11} ≃ {y : P3 // IsConj zK y ∨ IsConj zK⁻¹ y} :=
    Equiv.subtypeEquivRight fun x => ⟨ord11_conj, fun h => by
      rcases h with h | h
      · rw [orderOf_of_isConj h, zK_ord]
      · rw [orderOf_of_isConj h, hzi]⟩
  have hd : Disjoint (fun y : P3 => IsConj zK y) (fun y => IsConj zK⁻¹ y) := by
    rw [Pi.disjoint_iff]
    intro y
    rw [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩
    exact not_conj_z (h1.trans h2.symm)
  classical
  rw [Nat.card_congr (e.trans (subtypeOrEquiv _ _ hd)), Nat.card_sum, card_clz, card_clzi]

theorem cSzA : PHST.c = 5775 := Nat.eq_of_beq_eq_true PHSCl.cASz

theorem cSzB : PHSU.c = 15400 := Nat.eq_of_beq_eq_true PHSCl.cBSz

noncomputable abbrev xA (i : Nat) : Equiv.Perm (Fin 3850) := E (nfX 4 (PHSCl.XA i))

noncomputable abbrev xB (j : Nat) : Equiv.Perm (Fin 3850) := E (nfX 4 (PHSCl.XB j))

theorem inv_recA {i : Nat} (hi : i < 5775) :
    nfValidK 4 PHSC.LR (nfX 4 (PHSCl.XA i)) = true ∧ orderOf (xA i) = 2 := by
  have h := blk_spec (R := 4) (B := 512) (N := 3) (h := PHSCn.invA) (fun _ _ => rfl)
    PHSCn.invA_all (by norm_num) (by norm_num) (by omega : i < 3 * 4 * 512)
  exact invAt_spec tc hH hbs h (cSzA ▸ hi) fun hok =>
    nfElt_mem hsChainArrays (chainCheckFacts PairHS.chain_check.1) hsChain_valid.1 hok

theorem inv_recB {j : Nat} (hj : j < 15400) :
    nfValidK 4 PHSC.LR (nfX 4 (PHSCl.XB j)) = true ∧ orderOf (xB j) = 2 := by
  have h := blk_spec (R := 4) (B := 512) (N := 8) (h := PHSCn.invB) (fun _ _ => rfl)
    PHSCn.invB_all (by norm_num) (by norm_num) (by omega : j < 8 * 4 * 512)
  exact invAt_spec tc hH hbs h (cSzB ▸ hj) fun hok =>
    nfElt_mem hsChainArrays (chainCheckFacts PairHS.chain_check.1) hsChain_valid.1 hok

theorem xA_mem {i : Nat} (hi : i < 5775) : xA i ∈ P3 := E_mem (inv_recA hi).1
theorem xB_mem {j : Nat} (hj : j < 15400) : xB j ∈ P3 := E_mem (inv_recB hj).1

theorem key_recA {i : Nat} (hi : i < 5775) :
    PHSCl.KA i = keyL 3850 (PHSCn.nfp (nfX 4 (PHSCl.XA i))) PairHS.bs := by
  have h := blk_spec (R := 8) (B := 64) (N := 12) (h := PHSCl.recA) (fun _ _ => rfl)
    PHSCl.recA_all (by norm_num) (by norm_num) (by omega : i < 12 * 8 * 64)
  unfold recOKT at h
  rw [blt_true (cSzA ▸ hi)] at h
  change strictB (nfX 4 (PHSCl.XA i)) _ = true at h
  rw [strictB_val, bAnd_iff] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem key_recB {j : Nat} (hj : j < 15400) :
    PHSCl.KB j = keyL 3850 (PHSCn.nfp (nfX 4 (PHSCl.XB j))) PairHS.bs := by
  have h := blk_spec (R := 8) (B := 64) (N := 31) (h := PHSCl.recB) (fun _ _ => rfl)
    PHSCl.recB_all (by norm_num) (by norm_num) (by omega : j < 31 * 8 * 64)
  unfold recOKT at h
  rw [blt_true (cSzB ▸ hj)] at h
  change strictB (nfX 4 (PHSCl.XB j)) _ = true at h
  rw [strictB_val, bAnd_iff] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem joint_nodup :
    ((List.range 5775).map PHSCl.KA ++ (List.range 15400).map PHSCl.KB).Nodup := by
  have srt := keysK_sound (cs := [(PHST.c, PHSCl.KA), (PHSU.c, PHSCl.KB)]) (nB := 42) (R := 8)
    (B := 64) (by simp) (by decide) PHSCl.jsrt_all
  have hnd := nodup_of_strictInc_mergeSort srt
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, cSzA, cSzB] using hnd

theorem KA_inj {i j : Nat} (hi : i < 5775) (hj : j < 5775) (h : PHSCl.KA i = PHSCl.KA j) :
    i = j :=
  List.inj_on_of_nodup_map (List.nodup_append.1 joint_nodup).1 (List.mem_range.2 hi)
    (List.mem_range.2 hj) h

theorem KB_inj {i j : Nat} (hi : i < 15400) (hj : j < 15400) (h : PHSCl.KB i = PHSCl.KB j) :
    i = j :=
  List.inj_on_of_nodup_map (List.nodup_append.1 joint_nodup).2.1 (List.mem_range.2 hi)
    (List.mem_range.2 hj) h

theorem KAB_ne {i j : Nat} (hi : i < 5775) (hj : j < 15400) : PHSCl.KA i ≠ PHSCl.KB j :=
  (List.nodup_append.1 joint_nodup).2.2 _ (List.mem_map_of_mem (List.mem_range.2 hi)) _
    (List.mem_map_of_mem (List.mem_range.2 hj))

theorem keyA_eq {i j : Nat} (hi : i < 5775) (hj : j < 5775) (h : xA i = xA j) :
    PHSCl.KA i = PHSCl.KA j := by
  rw [key_recA hi, key_recA hj]
  refine keyL_congr 3850 fun b hb => ?_
  have h' : E (nfX 4 (PHSCl.XA i)) = E (nfX 4 (PHSCl.XA j)) := h
  rw [E_rep (inv_recA hi).1 b (hbs b hb), E_rep (inv_recA hj).1 b (hbs b hb), h']

theorem keyB_eq {i j : Nat} (hi : i < 15400) (hj : j < 15400) (h : xB i = xB j) :
    PHSCl.KB i = PHSCl.KB j := by
  rw [key_recB hi, key_recB hj]
  refine keyL_congr 3850 fun b hb => ?_
  have h' : E (nfX 4 (PHSCl.XB i)) = E (nfX 4 (PHSCl.XB j)) := h
  rw [E_rep (inv_recB hi).1 b (hbs b hb), E_rep (inv_recB hj).1 b (hbs b hb), h']

theorem keyAB_eq {i j : Nat} (hi : i < 5775) (hj : j < 15400) (h : xA i = xB j) :
    PHSCl.KA i = PHSCl.KB j := by
  rw [key_recA hi, key_recB hj]
  refine keyL_congr 3850 fun b hb => ?_
  have h' : E (nfX 4 (PHSCl.XA i)) = E (nfX 4 (PHSCl.XB j)) := h
  rw [E_rep (inv_recA hi).1 b (hbs b hb), E_rep (inv_recB hj).1 b (hbs b hb), h']

noncomputable def recOf : Fin 5775 ⊕ Fin 15400 → {x : P3 // orderOf x = 2}
  | .inl i => ⟨mk (xA i) (xA_mem i.2), by rw [Subgroup.orderOf_mk]; exact (inv_recA i.2).2⟩
  | .inr j => ⟨mk (xB j) (xB_mem j.2), by rw [Subgroup.orderOf_mk]; exact (inv_recB j.2).2⟩

abbrev valI (g : {x : P3 // orderOf x = 2}) : Equiv.Perm (Fin 3850) := (g : P3)

theorem recOf_bij : Function.Bijective recOf := by
  have hinj : Function.Injective recOf := by
    intro s t h
    have hv := congrArg valI h
    rcases s with i | i <;> rcases t with j | j
    · have h' : xA i = xA j := hv
      exact congrArg Sum.inl (Fin.ext (KA_inj i.2 j.2 (keyA_eq i.2 j.2 h')))
    · have h' : xA i = xB j := hv
      exact absurd (keyAB_eq i.2 j.2 h') (KAB_ne i.2 j.2)
    · have h' : xB i = xA j := hv
      exact absurd (keyAB_eq j.2 i.2 h'.symm) (KAB_ne j.2 i.2)
    · have h' : xB i = xB j := hv
      exact congrArg Sum.inr (Fin.ext (KB_inj i.2 j.2 (keyB_eq i.2 j.2 h')))
  exact hinj.bijective_of_nat_card_le (by rw [card_two, Nat.card_sum, Nat.card_fin, Nat.card_fin])

theorem rec_cover {x : P3} (hx : orderOf x = 2) :
    (∃ i < 5775, xA i = x) ∨ ∃ j < 15400, xB j = x := by
  obtain ⟨s, hs⟩ := recOf_bij.2 ⟨x, hx⟩
  have hv := congrArg valI hs
  rcases s with i | j
  · exact Or.inl ⟨i, i.2, hv⟩
  · exact Or.inr ⟨j, j.2, hv⟩

def Acond (x w : P3) : Prop :=
  orderOf x = 2 ∧ orderOf (x * w) = 5 ∧ orderOf (w * x * w⁻¹ * x) = 5

theorem acond_coe (x w : P3) : Acond x w ↔ orderOf x = 2 ∧
    orderOf ((x : Equiv.Perm (Fin 3850)) * w) = 5 ∧
    orderOf ((w : Equiv.Perm (Fin 3850)) * x * (w : Equiv.Perm (Fin 3850))⁻¹ * x) = 5 := by
  unfold Acond
  rw [← Subgroup.orderOf_coe (x * w), ← Subgroup.orderOf_coe (w * x * w⁻¹ * x)]
  rfl

theorem scan_part {w : Equiv.Perm (Fin 3850)} (hw : w ∈ P3) {Z ZI : Nat → Nat}
    (hZ : RepF 3850 Z w) (hZI : RepF 3850 ZI w⁻¹) {X : Nat → Nat} {c N m : Nat} (hc : c = N)
    (hV : ∀ i < c, nfValidK 4 PHSC.LR (nfX 4 (X i)) = true)
    (hE : ∀ i < c, E (nfX 4 (X i)) ∈ P3) {V : Nat → Nat} {a : Nat}
    (hs : sumN (m * 512) (scanHSAt 12 PHST.NR PHST.NR PHST.LT PHST.PT PHSCn.bs c X Z ZI) =
      sumN m V) (ha : sumN m V = a) (hN : N ≤ m * 512) :
    (Finset.filter (fun i => orderOf (E (nfX 4 (X i)) * w) = 5 ∧
      orderOf (w * E (nfX 4 (X i)) * w⁻¹ * E (nfX 4 (X i))) = 5) (Finset.range N)).card = a := by
  classical
  rw [ha, sumN_finset] at hs
  have hs2 : ∑ i ∈ Finset.range (m * 512), (if i < N ∧ orderOf (E (nfX 4 (X i)) * w) = 5 ∧
      orderOf (w * E (nfX 4 (X i)) * w⁻¹ * E (nfX 4 (X i))) = 5 then 1 else 0) = a := by
    rw [← hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [scanHSAt_eq tc' hH' hbs' hZ hZI hw (fun hi => hV i hi) (fun hi => hE i hi), hc]
  rw [← Finset.card_filter] at hs2
  rw [← hs2]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, h⟩
    exact ⟨by omega, hi, h⟩
  · rintro ⟨-, hi, h⟩
    exact ⟨hi, h⟩

theorem scan_count (w : P3) {Z ZI : Nat → Nat} (hZ : RepF 3850 Z w)
    (hZI : RepF 3850 ZI (w⁻¹ : P3)) {VA VB : Nat → Nat}
    (hVA : ∀ g < 3, ∀ r < 4, Nat.beq (PHSCn.scAt PHSCl.XA PHST.c Z ZI (Nat.add (Nat.mul g 4) r))
      (VA (Nat.add (Nat.mul g 4) r)) = true)
    (hVB : ∀ g < 8, ∀ r < 4, Nat.beq (PHSCn.scAt PHSCl.XB PHSU.c Z ZI (Nat.add (Nat.mul g 4) r))
      (VB (Nat.add (Nat.mul g 4) r)) = true) {a b : Nat} (ha : sumN 12 VA = a)
    (hb : sumN 32 VB = b) :
    Nat.card {x : P3 // Acond x w} = a + b := by
  classical
  have hZI' : RepF 3850 ZI (w : Equiv.Perm (Fin 3850))⁻¹ := hZI
  have hsA := chunk_sum 12 512 (scanHSAt 12 PHST.NR PHST.NR PHST.LT PHST.PT PHSCn.bs PHST.c
    PHSCl.XA Z ZI) VA fun q hq => by
      have := Nat.eq_of_beq_eq_true (hVA (q / 4) (by omega) (q % 4) (Nat.mod_lt _ (by norm_num)))
      rw [split] at this
      exact this
  have hsB := chunk_sum 32 512 (scanHSAt 12 PHST.NR PHST.NR PHST.LT PHST.PT PHSCn.bs PHSU.c
    PHSCl.XB Z ZI) VB fun q hq => by
      have := Nat.eq_of_beq_eq_true (hVB (q / 4) (by omega) (q % 4) (Nat.mod_lt _ (by norm_num)))
      rw [split] at this
      exact this
  have cA := scan_part w.2 hZ hZI' cSzA (fun i hi => (inv_recA (cSzA ▸ hi)).1)
    (fun i hi => xA_mem (cSzA ▸ hi)) hsA ha (by norm_num)
  have cB := scan_part w.2 hZ hZI' cSzB (fun i hi => (inv_recB (cSzB ▸ hi)).1)
    (fun i hi => xB_mem (cSzB ▸ hi)) hsB hb (by norm_num)
  set FA := Finset.filter (fun i => orderOf (E (nfX 4 (PHSCl.XA i)) * (w : Equiv.Perm (Fin 3850))) = 5 ∧
      orderOf ((w : Equiv.Perm (Fin 3850)) * E (nfX 4 (PHSCl.XA i)) * (w : Equiv.Perm (Fin 3850))⁻¹ *
        E (nfX 4 (PHSCl.XA i))) = 5) (Finset.range 5775) with hFA
  set FB := Finset.filter (fun i => orderOf (E (nfX 4 (PHSCl.XB i)) * (w : Equiv.Perm (Fin 3850))) = 5 ∧
      orderOf ((w : Equiv.Perm (Fin 3850)) * E (nfX 4 (PHSCl.XB i)) * (w : Equiv.Perm (Fin 3850))⁻¹ *
        E (nfX 4 (PHSCl.XB i))) = 5) (Finset.range 15400) with hFB
  let f : FA ⊕ FB → {x : P3 // Acond x w}
    | .inl i => ⟨mk (xA i.1) (xA_mem (Finset.mem_range.1 (Finset.mem_filter.1 i.2).1)),
        (acond_coe _ _).2 ⟨by
          rw [Subgroup.orderOf_mk]
          exact (inv_recA (Finset.mem_range.1 (Finset.mem_filter.1 i.2).1)).2,
          (Finset.mem_filter.1 i.2).2⟩⟩
    | .inr j => ⟨mk (xB j.1) (xB_mem (Finset.mem_range.1 (Finset.mem_filter.1 j.2).1)),
        (acond_coe _ _).2 ⟨by
          rw [Subgroup.orderOf_mk]
          exact (inv_recB (Finset.mem_range.1 (Finset.mem_filter.1 j.2).1)).2,
          (Finset.mem_filter.1 j.2).2⟩⟩
  let valA : {x : P3 // Acond x w} → Equiv.Perm (Fin 3850) := fun g => ((g : P3) : _)
  have hb' : Function.Bijective f := by
    refine ⟨fun s t h => ?_, fun x => ?_⟩
    · have hv := congrArg valA h
      rcases s with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rcases t with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hi' := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
        have hj' := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
        have h' : xA i = xA j := hv
        exact congrArg Sum.inl (Subtype.ext (KA_inj hi' hj' (keyA_eq hi' hj' h')))
      · have hi' := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
        have hj' := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
        have h' : xA i = xB j := hv
        exact absurd (keyAB_eq hi' hj' h') (KAB_ne hi' hj')
      · have hi' := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
        have hj' := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
        have h' : xB i = xA j := hv
        exact absurd (keyAB_eq hj' hi' h'.symm) (KAB_ne hj' hi')
      · have hi' := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
        have hj' := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
        have h' : xB i = xB j := hv
        exact congrArg Sum.inr (Subtype.ext (KB_inj hi' hj' (keyB_eq hi' hj' h')))
    · have hx := (acond_coe _ _).1 x.2
      rcases rec_cover hx.1 with ⟨i, hi, he⟩ | ⟨j, hj, he⟩
      · have he' : E (nfX 4 (PHSCl.XA i)) = ((x : P3) : Equiv.Perm (Fin 3850)) := he
        refine ⟨.inl ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, ?_⟩⟩, Subtype.ext
          (Subtype.ext he)⟩
        rw [he']
        exact hx.2
      · have he' : E (nfX 4 (PHSCl.XB j)) = ((x : P3) : Equiv.Perm (Fin 3850)) := he
        refine ⟨.inr ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ?_⟩⟩, Subtype.ext
          (Subtype.ext he)⟩
        rw [he']
        exact hx.2
  rw [← Nat.card_eq_of_bijective f hb', Nat.card_sum, Nat.card_eq_finsetCard,
    Nat.card_eq_finsetCard, cA, cB]

theorem acond_conj (c x w : P3) : Acond (MulAut.conj c x) (MulAut.conj c w) ↔ Acond x w := by
  unfold Acond
  simp only [← map_inv, ← map_mul, MulEquiv.orderOf_eq]

theorem ziRepK : RepF 3850 PHSCn.ziP ((zK⁻¹ : P3) : Equiv.Perm (Fin 3850)) := by
  have e : ((zK⁻¹ : P3) : Equiv.Perm (Fin 3850)) = ziE := by
    rw [Subgroup.coe_inv, ziE_eq]
  rw [e]
  exact ziRep

theorem K_val {w : P3} (hw : orderOf w = 11) : Nat.card {x : P3 // Acond x w} = 132 := by
  have hz : Nat.card {x : P3 // Acond x zK} = 132 :=
    scan_count zK (Z := PHSCn.zP) (ZI := PHSCn.ziP) zRep ziRepK PHSCn.scA_all PHSCn.scB_all
      (Nat.eq_of_beq_eq_true PHSCn.sA) (Nat.eq_of_beq_eq_true PHSCn.sB)
  have hzi : Nat.card {x : P3 // Acond x zK⁻¹} = 132 :=
    scan_count zK⁻¹ (Z := PHSCn.ziP) (ZI := PHSCn.zP) ziRepK (by rw [inv_inv]; exact zRep)
      PHSCn.scAI_all PHSCn.scBI_all (Nat.eq_of_beq_eq_true PHSCn.sAI)
      (Nat.eq_of_beq_eq_true PHSCn.sBI)
  have hc : ∀ v : P3, IsConj v w →
      Nat.card {x : P3 // Acond x w} = Nat.card {x : P3 // Acond x v} := by
    intro v h
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    exact (Nat.card_congr ((MulAut.conj c).toEquiv.subtypeEquiv fun x =>
      (acond_conj c x v).symm)).symm
  rcases ord11_conj hw with h | h
  · rw [hc _ h, hz]
  · rw [hc _ h, hzi]

theorem patRel_iff (x y : P3) : PatRel PairHS.conds x y ↔
    orderOf (x * y) = 11 ∧ orderOf (x * (y * (x * (y * (y * (y * y)))))) = 5 := by
  simp [PatRel, PairHS.conds, PairHS.commPat]

theorem pow4_eq {y : P3} (hy : orderOf y = 5) : y * (y * (y * y)) = y⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have h : y ^ 5 = 1 := hy ▸ pow_orderOf_eq_one y
  have e : y * (y * (y * y)) * y = y ^ 5 := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e, h]

theorem card_pairs : Nat.card {p : P3 × P3 // orderOf p.1 = 2 ∧ orderOf p.2 = 5 ∧
    PatRel PairHS.conds p.1 p.2} = 1064448000 := by
  classical
  have hxa : ∀ x : P3, orderOf x = 2 → ∀ a, x * (x * a) = a := fun x hx a => by
    rw [← mul_assoc, ← pow_two, ← hx, pow_orderOf_eq_one, one_mul]
  have fwd : ∀ x y : P3, orderOf x = 2 → orderOf y = 5 →
      x * y * x * (x * y)⁻¹ * x = x * (y * (x * (y * (y * (y * y))))) := fun x y hx hy => by
    rw [pow4_eq hy]
    group
  let e : {p : P3 × P3 // orderOf p.1 = 2 ∧ orderOf p.2 = 5 ∧ PatRel PairHS.conds p.1 p.2} ≃
      Σ w : {w : P3 // orderOf w = 11}, {x : P3 // Acond x w} :=
    { toFun := fun p => ⟨⟨p.1.1 * p.1.2, ((patRel_iff _ _).1 p.2.2.2).1⟩, ⟨p.1.1, p.2.1, by
          rw [hxa _ p.2.1]; exact p.2.2.1, by
          rw [fwd _ _ p.2.1 p.2.2.1]
          exact ((patRel_iff _ _).1 p.2.2.2).2⟩⟩
      invFun := fun q => ⟨(q.2.1, q.2.1 * q.1.1), q.2.2.1, q.2.2.2.1, (patRel_iff _ _).2
        ⟨by rw [hxa _ q.2.2.1]; exact q.1.2, by
          rw [← fwd _ _ q.2.2.1 q.2.2.2.1, hxa _ q.2.2.1]
          exact q.2.2.2.2⟩⟩
      left_inv := fun p => by
        apply Subtype.ext
        simp only [hxa _ p.2.1]
      right_inv := fun q => by
        rcases q with ⟨⟨w, hw⟩, ⟨x, hx⟩⟩
        exact Sigma.subtype_ext (Subtype.ext (hxa x hx.1 w)) rfl }
  have : Fintype {w : P3 // orderOf w = 11} := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma]
  rw [Finset.sum_congr rfl fun w _ => K_val w.2, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_eleven]
  rfl

theorem facts : (PairHS.parCount (ordPred PairHS.bs 2) PairHS.blocks = 21175) ∧
    (PairHS.parCount (ordPred PairHS.bs 5) PairHS.blocks = 2010624) ∧
    ((PairHS.cl.map fun c => c.2.1.size *
      PairHS.parCount (pairPred PairHS.bs 5 c.1 PairHS.conds) PairHS.blocks).sum =
        1064448000) := by
  have c2 : PairHS.parCount (ordPred PairHS.bs 2) PairHS.blocks = 21175 := by
    rw [← hs_card_order 2 (by norm_num)]
    exact card_two
  refine ⟨c2, ?_, ?_⟩
  · rw [← hs_card_order 5 (by norm_num)]
    exact card_five
  · obtain ⟨h1', h2, h3, h4⟩ := PairHS.classes
    have h4' : (PairHS.cl.map fun c => c.2.1.size).sum =
        countW (fun w => ordB PairHS.bs w 2) (blocksOf 3850 (rawLevels 3850 hsStrongArrs
          PairHS.baseArr) PairHS.groups) [] := by
      rw [h4, ← c2, PairHS.parCount_eq]
      rfl
    have h := card_pairs_eq_classTotalNF (mx := 2) (my := 5) (conds := PairHS.conds) hsChainArrays
      (by norm_num) PairHS.chain_check.1 hs_bs_eq hs_groups (by norm_num) (by norm_num) (by decide)
      hs_gens PairHS.cl hs_reps h1' h2 h3 h4'
    rw [card_pairs] at h
    rw [h]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    rw [PairHS.parCount_eq]
    rfl

end HS

end CertificateChecks.KernelSporSch.PHSCount

end
