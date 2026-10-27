
module

public import Certificates.Kernel.SporSch.PairHe.CntSmall
public import Certificates.Kernel.SporSch.PairHe.Check2224
public import CFSG.Certificates.Kernel.SporSch.PairHeCntSound
public import CFSG.Certificates.Kernel.SporSch.SylowSeventeen
public import CFSG.Sporadic.Schreier.PairOuterPat

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PHePart

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Certificates
open CFSG.Certificates.Native CFSG.Sporadic.HeldB
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSporSch.PJ3Group CertificateChecks.KernelSporSch.PHSClass
open CertificateChecks.KernelSporSch.PHeCount

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

theorem keyL_keyElt {n : Nat} {f : Nat → Nat} {g : Equiv.Perm (Fin n)} (hf : RepF n f g) :
    ∀ {bs : List Nat}, (∀ b ∈ bs, b < n) → keyL n f bs = keyElt n bs g
  | [], _ => rfl
  | b :: bs, h => by
    change strictN (keyL n f bs) (fun r => Nat.add (f b) (Nat.mul n r)) = _
    rw [strictN_val, keyL_keyElt hf fun c hc => h c (List.mem_cons_of_mem b hc), keyElt, keyElt,
      List.map_cons, imgKey, imgKey, List.foldr_cons, dite_eq_left (h b List.mem_cons_self),
      hf b (h b List.mem_cons_self)]
    rfl

def Qr {G : Type*} [Group G] (x y : G) : Prop := orderOf y = 7 ∧ PatRel PairHe.conds x y

def TestG {G : Type*} [Group G] (x j : G) : Prop :=
  orderOf (x * j) = 7 ∧ orderOf (j * x * j⁻¹ * x) = 6 ∧ orderOf (j * x * j) = 12 ∧
    orderOf (j * j * x * j) = 15

theorem qr_conj {G : Type*} [Group G] (g x y : G) :
    Qr (g * x * g⁻¹) (g * y * g⁻¹) ↔ Qr x y := by
  unfold Qr
  rw [patRel_conj, ← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem conds_eq : PairHe.conds = [([false, true], 17), (PairHe.commPat, 6), (PairHe.pat12, 12),
    (PairHe.pat15, 15)] := rfl

theorem qr_iff {G : Type*} [Group G] {x j : G} (hx : orderOf x = 2) (hj : orderOf j = 17) :
    Qr x (x⁻¹ * j) ↔ TestG x j := by
  have hxi : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← hx, pow_orderOf_eq_one])
  set y := x⁻¹ * j with hy
  have e1 : ([false, true].map fun b => if b then y else x).prod = j := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Bool.false_eq_true,
      ↓reduceIte, mul_one, hy]
    group
  have e3 : (PairHe.pat12.map fun b => if b then y else x).prod = j * x * j := by
    simp only [PairHe.pat12, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, ↓reduceIte, mul_one, hy]
    conv_rhs => rw [← hxi]
    group
  have e4 : (PairHe.pat15.map fun b => if b then y else x).prod = j * j * x * j := by
    simp only [PairHe.pat15, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, ↓reduceIte, mul_one, hy]
    conv_rhs => rw [← hxi]
    group
  have e2 : orderOf y = 7 →
      (PairHe.commPat.map fun b => if b then y else x).prod = j * x * j⁻¹ * x := by
    intro h7
    have h6 : y * (y * (y * (y * (y * y)))) = y⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have e : y * (y * (y * (y * (y * y)))) * y = y ^ 7 := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e, ← h7, pow_orderOf_eq_one]
    simp only [PairHe.commPat, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, ↓reduceIte, mul_one]
    rw [h6, hy]
    group
  have hy7 : orderOf y = orderOf (x * j) := by rw [hy, hxi]
  unfold Qr TestG PatRel
  rw [conds_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  rw [e1, e3, e4, hj, hy7]
  constructor
  · rintro ⟨h7, -, h2, h3, h4⟩
    rw [hy7] at e2
    rw [e2 h7] at h2
    exact ⟨h7, h2, h3, h4⟩
  · rintro ⟨h7, h2, h3, h4⟩
    rw [hy7] at e2
    exact ⟨h7, rfl, by rw [e2 h7]; exact h2, h3, h4⟩

section He

theorem repsF : nfValidK 5 HeC.LR PHeN.n0 = true ∧ nfValidK 5 HeC.LR PHeN.n1 = true ∧
    nfValidK 5 HeC.LR PHeN.n2 = true ∧ ordPL PHeSn.bs PHeCn.zP 17 = true ∧
    Nat.beq (PHeCn.zP 0) 1 = true ∧
    eqOnL PHeSn.bs (fun b => PHeCn.zP (PHeCn.ziP b)) (fun x => x) = true ∧
    eqOnL PHeSn.bs (fun b => PHeSn.nfp PHeN.n2 (PHeCn.zP b))
      (fun b => PHeCn.zP (PHeCn.zP (PHeSn.nfp PHeN.n2 b))) = true := by
  have h := PHeCn.reps
  unfold PHeCn.repsB at h
  simpa only [bAnd_iff, and_assoc] using h

theorem bindAll {g : Nat} (hg : g < 2) {F P : Nat}
    (hFP : ∀ r, PHeCn.bindB g r = PHeCn.bindR F P (Nat.mul r 833)) :
    ∀ x < 8330, bind5At 8330 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT F P x = true := by
  intro x hx
  have h := PHeCn.bindB_all g hg (x / 833) (by change x / 833 < 10; omega)
  rw [hFP] at h
  have h2 := allBlk_spec h (x % 833) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 833) 833) (x % 833) = x := split
  rwa [e] at h2

noncomputable abbrev zE : Equiv.Perm (Fin 8330) := E PHeN.n0
noncomputable abbrev ziE : Equiv.Perm (Fin 8330) := E PHeN.n1
noncomputable abbrev nuE : Equiv.Perm (Fin 8330) := E PHeN.n2

theorem zRep : RepF 8330 PHeCn.zP zE :=
  bind5_spec tc repsF.1 (bindAll (g := 0) (by norm_num) fun _ => rfl)

theorem ziRep : RepF 8330 PHeCn.ziP ziE :=
  bind5_spec tc repsF.2.1 (bindAll (g := 1) (by norm_num) fun _ => rfl)

theorem zMem : zE ∈ P3 := E_mem repsF.1
theorem ziMem : ziE ∈ P3 := E_mem repsF.2.1
theorem nuMem : nuE ∈ P3 := E_mem repsF.2.2.1

theorem zOrd : orderOf zE = 17 :=
  (ordPL_iff hH hbs zRep zMem (by norm_num)).1 repsF.2.2.2.1

theorem ziE_eq : ziE = zE⁻¹ :=
  eq_inv_of_mul_eq_one_right (eq_of_eqOnL hH (zRep.comp ziRep) RepF.one (P3.mul_mem zMem ziMem)
    P3.one_mem repsF.2.2.2.2.2.1)

theorem nuEq : nuE * zE = zE * (zE * nuE) :=
  eq_of_eqOnL hH ((E_rep repsF.2.2.1).comp zRep) (zRep.comp (zRep.comp (E_rep repsF.2.2.1)))
    (P3.mul_mem nuMem zMem) (P3.mul_mem zMem (P3.mul_mem zMem nuMem)) repsF.2.2.2.2.2.2

noncomputable abbrev zK : P3 := mk zE zMem
noncomputable abbrev nuK : P3 := mk nuE nuMem

theorem zK_ord : orderOf zK = 17 := by
  rw [Subgroup.orderOf_mk]
  exact zOrd

theorem nuK_eq : nuK * zK * nuK⁻¹ = zK ^ 2 := by
  rw [mul_inv_eq_iff_eq_mul, pow_two]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul]
  rw [nuEq, mul_assoc]

theorem hdvd17 : ¬17 ^ 2 ∣ Nat.card P3 := by
  rw [card_P3]
  norm_num

theorem ord17_conj {x : P3} (hx : orderOf x = 17) : IsConj zK x ∨ IsConj (zK ^ 3) x := by
  have hp : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact SylowCount.cover_seventeen zK_ord nuK_eq (SylowCount.conj_pow_of_orderOf hdvd17 zK_ord hx)
    hx

theorem zK3_ord : orderOf (zK ^ 3) = 17 := by
  rw [Nat.Coprime.orderOf_pow (by rw [zK_ord]; norm_num), zK_ord]

theorem rec_at {X K : Nat → Nat} {c nB : Nat}
    (h : ∀ g < nB, ∀ r < 8, allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
      (recOKT 8330 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT 5 PairHe.bs (fun t => rcnt (HeC.LR t)) X K
        c) 64 = true) {i : Nat} (hi : i < c) (hic : i < nB * 8 * 64) :
    nfValidK 5 HeC.LR (nfX 5 (X i)) = true ∧
      K i = keyL 8330 (PHeSn.nfp (nfX 5 (X i))) PairHe.bs := by
  have h1 := blk_spec (R := 8) (B := 64) (N := nB) (f := recOKT 8330 14 PHeT.NR PHeT.NR PHeT.LT
    PHeT.PT 5 PairHe.bs (fun t => rcnt (HeC.LR t)) X K c) (h := fun g r => allBlk
      (Nat.mul (Nat.add (Nat.mul g 8) r) 64) (recOKT 8330 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT 5
        PairHe.bs (fun t => rcnt (HeC.LR t)) X K c) 64) (fun _ _ => rfl) h (by norm_num)
    (by norm_num) hic
  unfold recOKT at h1
  rw [blt_true hi] at h1
  change strictB (nfX 5 (X i)) _ = true at h1
  rw [strictB_val, bAnd_iff] at h1
  exact ⟨h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem entry_key {Ecl : Array (Array Nat)} {K : Nat → Nat} {c : Nat}
    (h : Ecl.toList.map (fun nf => imgKey 8330 (baseImgs PairHe.bs
      (nfWord (rawLevels 8330 heStrongArrs heBase.toArray) nf))) = (List.range c).map K)
    {i : Nat} (hi : i < c) (hiE : i < Ecl.size) :
    imgKey 8330 (baseImgs PairHe.bs (nfWord (rawLevels 8330 heStrongArrs heBase.toArray)
      Ecl[i]!)) = K i := by
  have h1 := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hiE,
    Option.map_some, List.getElem?_range hi] at h1
  rw [getElem!_pos Ecl i hiE]
  exact Option.some_injective _ h1

theorem card_class_filter {X K : Nat → Nat} {N nB : Nat} {rep : List (Array Nat)}
    {x₀ : Equiv.Perm (Fin 8330)} (hrep : RepW 8330 rep x₀) (hx₀ : x₀ ∈ P3)
    {Ecl : Array (Array Nat)} {par lab : Array Nat}
    (hok : closureOK (rawLevels 8330 heStrongArrs heBase.toArray) PairHe.bs PairHe.gens
      PairHe.gensInv rep Ecl par lab = true) (hsz : Ecl.size = N)
    (hkeys : Ecl.toList.map (fun nf => imgKey 8330 (baseImgs PairHe.bs
      (nfWord (rawLevels 8330 heStrongArrs heBase.toArray) nf))) = (List.range N).map K)
    (hnd : ((List.range N).map K).Nodup)
    (hrec : ∀ g < nB, ∀ r < 8, allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
      (recOKT 8330 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT 5 PairHe.bs (fun t => rcnt (HeC.LR t)) X K
        N) 64 = true) (hN : N ≤ nB * 8 * 64)
    (hcard : Nat.card {y : P3 // IsConj (mk x₀ hx₀) y} = N)
    (Pr : Equiv.Perm (Fin 8330) → Prop) [DecidablePred Pr] :
    Nat.card {x : P3 // IsConj (mk x₀ hx₀) x ∧ Pr x} =
      ((Finset.range N).filter fun i => Pr (E (nfX 5 (X i)))).card := by
  have hspec := closureOK_spec heChainArrays (chainCheckFacts heChain_check.1) heChain_valid.1 hH
    hbs he_gens hrep hx₀ hok
  have hR : ∀ i < N, nfValidK 5 HeC.LR (nfX 5 (X i)) = true ∧
      K i = keyL 8330 (PHeSn.nfp (nfX 5 (X i))) PairHe.bs := fun i hi =>
    rec_at hrec hi (by omega)
  have hmem : ∀ i < N, E (nfX 5 (X i)) ∈ P3 := fun i hi => E_mem (hR i hi).1
  have heq : ∀ i < N, E (nfX 5 (X i)) =
      nfElt 8330 heStrongArrs heBase.toArray Ecl[i]! := fun i hi => by
    have hiE : i < Ecl.size := hsz ▸ hi
    have hok' := (hspec i hiE).1
    refine keyElt_inj hH hbs (hmem i hi)
      (nfElt_mem heChainArrays (chainCheckFacts heChain_check.1) heChain_valid.1 hok') ?_
    exact ((keyL_keyElt (E_rep (hR i hi).1) hbs).symm.trans (hR i hi).2.symm).trans
      ((entry_key hkeys hi hiE).symm.trans (imgKey_baseImgs hbs (repW_nfWord heChainArrays
        (chainCheckFacts heChain_check.1) hok')))
  have hconj : ∀ i (hi : i < N), IsConj (mk x₀ hx₀) (mk (E (nfX 5 (X i))) (hmem i hi)) := by
    intro i hi
    obtain ⟨c, hc, hce⟩ := (hspec i (hsz ▸ hi)).2
    refine isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [heq i hi, hce]
  have hinj : ∀ i < N, ∀ j < N, E (nfX 5 (X i)) = E (nfX 5 (X j)) → i = j := by
    intro i hi j hj h
    have hk : K i = K j := by
      rw [(hR i hi).2, (hR j hj).2, keyL_keyElt (E_rep (hR i hi).1) hbs,
        keyL_keyElt (E_rep (hR j hj).1) hbs]
      exact congrArg (keyElt 8330 PairHe.bs) h
    exact List.inj_on_of_nodup_map hnd (List.mem_range.2 hi) (List.mem_range.2 hj) hk
  let f : Fin N → {y : P3 // IsConj (mk x₀ hx₀) y} := fun i =>
    ⟨mk (E (nfX 5 (X i))) (hmem i i.2), hconj i i.2⟩
  have hfb : Function.Bijective f := by
    refine Function.Injective.bijective_of_nat_card_le (fun i j h => Fin.ext ?_)
      (by rw [hcard, Nat.card_fin])
    exact hinj i i.2 j j.2 (congrArg (fun y : {y : P3 // IsConj (mk x₀ hx₀) y} =>
      ((y : P3) : Equiv.Perm (Fin 8330))) h)
  let F := (Finset.range N).filter fun i => Pr (E (nfX 5 (X i)))
  let g : F → {x : P3 // IsConj (mk x₀ hx₀) x ∧ Pr x} := fun i =>
    ⟨mk (E (nfX 5 (X i.1))) (hmem i.1 (Finset.mem_range.1 (Finset.mem_filter.1 i.2).1)),
      hconj i.1 (Finset.mem_range.1 (Finset.mem_filter.1 i.2).1), (Finset.mem_filter.1 i.2).2⟩
  have hgb : Function.Bijective g := by
    refine ⟨fun i j h => Subtype.ext ?_, fun x => ?_⟩
    · exact hinj i.1 (Finset.mem_range.1 (Finset.mem_filter.1 i.2).1) j.1
        (Finset.mem_range.1 (Finset.mem_filter.1 j.2).1)
        (congrArg (fun y : {x : P3 // IsConj (mk x₀ hx₀) x ∧ Pr x} =>
          ((y : P3) : Equiv.Perm (Fin 8330))) h)
    · obtain ⟨i, hi⟩ := hfb.2 ⟨x.1, x.2.1⟩
      have hv : E (nfX 5 (X i.1)) = ((x : P3) : Equiv.Perm (Fin 8330)) :=
        congrArg (fun y : {y : P3 // IsConj (mk x₀ hx₀) y} => ((y : P3) : Equiv.Perm (Fin 8330))) hi
      refine ⟨⟨i.1, Finset.mem_filter.2 ⟨Finset.mem_range.2 i.2, ?_⟩⟩, Subtype.ext
        (Subtype.ext hv)⟩
      rw [hv]
      exact x.2.2
  rw [← Nat.card_eq_finsetCard]
  exact (Nat.card_eq_of_bijective g hgb).symm

theorem tc' : TabChain 8330 14 9 5 HeC.BP 131 64 PHeT.NR PHeT.NR 147 1024 9 1024 HeC.S HeC.SI
    HeC.LR PHeT.Ts PHeT.LT PHeT.PT PHeT.QT heStrongArrs heBase.toArray PHeSn.bs := tc

theorem hH' : BaseFaithful P3 PHeSn.bs := hH

open scoped Classical in
theorem scan_part {j : Equiv.Perm (Fin 8330)} (hj : j ∈ P3) {Z ZI : Nat → Nat}
    (hZ : RepF 8330 Z j) (hZI : RepF 8330 ZI j⁻¹) {X : Nat → Nat} {c m : Nat}
    (hV : ∀ i < c, nfValidK 5 HeC.LR (nfX 5 (X i)) = true) {V : Nat → Nat} {a : Nat}
    (hs : ∀ q < m, PHeCn.scAt X c Z ZI q = V q) (ha : sumN m V = a) (hN : c ≤ m * 512) :
    ((Finset.range c).filter fun i => TestG (E (nfX 5 (X i))) j).card = a := by
  classical
  have hs1 := chunk_sum m 512 (scanHeAt 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT PHeSn.bs c X Z ZI) V
    hs
  rw [ha, sumN_finset] at hs1
  have hs2 : ∑ i ∈ Finset.range (m * 512), (if i < c ∧ TestG (E (nfX 5 (X i))) j then 1 else 0) =
      a := by
    rw [← hs1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [scanHeAt_eq tc' hH' hbs' hZ hZI hj (fun hi => hV i hi) (fun hi => E_mem (hV i hi))]
    exact if_congr Iff.rfl rfl rfl
  rw [← Finset.card_filter] at hs2
  rw [← hs2]
  refine congrArg Finset.card ?_
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, h⟩
    exact ⟨by omega, hi, h⟩
  · rintro ⟨-, hi, h⟩
    exact ⟨hi, h⟩

theorem testG_coe (x j : P3) :
    TestG x j ↔ TestG (x : Equiv.Perm (Fin 8330)) (j : Equiv.Perm (Fin 8330)) := by
  simp only [TestG, ← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv]

theorem z3Rep : RepF 8330 PHeCn.z3P ((zK ^ 3 : P3) : Equiv.Perm (Fin 8330)) :=
  (zRep.comp (zRep.comp zRep)).congr (by
    rw [SubmonoidClass.coe_pow]
    change zE * (zE * zE) = zE ^ 3
    rw [pow_three])

theorem z3iRep : RepF 8330 PHeCn.z3iP ((zK ^ 3 : P3) : Equiv.Perm (Fin 8330))⁻¹ :=
  (ziRep.comp (ziRep.comp ziRep)).congr (by
    rw [SubmonoidClass.coe_pow, ziE_eq]
    change zE⁻¹ * (zE⁻¹ * zE⁻¹) = (zE ^ 3)⁻¹
    group)

theorem ziRepK : RepF 8330 PHeCn.ziP ((zK : P3) : Equiv.Perm (Fin 8330))⁻¹ := by
  have e : ((zK : P3) : Equiv.Perm (Fin 8330))⁻¹ = ziE := by
    rw [ziE_eq]
  rw [e]
  exact ziRep

theorem partners_le (a : P3) {KZ KZ3 : Nat}
    (hKZ : Nat.card {x : P3 // IsConj a x ∧ Qr x (x⁻¹ * zK)} = KZ)
    (hKZ3 : Nat.card {x : P3 // IsConj a x ∧ Qr x (x⁻¹ * zK ^ 3)} = KZ3) :
    17 * (Nat.card {y : P3 // IsConj a y} * Nat.card {y : P3 // Qr a y}) ≤
      4030387200 * (KZ + KZ3) := by
  classical
  have : Fintype P3 := Fintype.ofFinite _
  have fc : ∀ (p : P3 → Prop) [DecidablePred p],
      (Finset.univ.filter p).card = Nat.card {x // p x} := fun p _ => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hZr : ∀ g x : P3, orderOf (g * x * g⁻¹) = 17 ↔ orderOf x = 17 := fun g x => by
    rw [SylowCount.orderOf_conj']
  have hZ : ∀ x : P3, orderOf x = 17 → ∃ j ∈ [zK, zK ^ 3], IsConj j x := fun x hx => by
    rcases ord17_conj hx with h | h
    · exact ⟨zK, List.mem_cons_self, h⟩
    · exact ⟨zK ^ 3, by simp, h⟩
  have h := SylowCount.pair_count_le a Qr qr_conj (fun x => orderOf x = 17) hZr [zK, zK ^ 3] hZ
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, fc] at h
  have hq : ∀ y : P3, (orderOf (a * y) = 17 ∧ Qr a y) ↔ Qr a y := fun y => by
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    have h1 := h.2 ([false, true], 17) (by rw [conds_eq]; exact List.mem_cons_self)
    simpa using h1
  rw [Nat.card_congr (Equiv.subtypeEquivRight hq), hKZ, hKZ3] at h
  have hG : Fintype.card P3 = 4030387200 := by rw [← Nat.card_eq_fintype_card, card_P3]
  have c1 := SylowCount.card_class_mul_le zK
  have c3 := SylowCount.card_class_mul_le (zK ^ 3)
  rw [zK_ord, hG, fc] at c1
  rw [zK3_ord, hG, fc] at c3
  calc 17 * (Nat.card {y : P3 // IsConj a y} * Nat.card {y : P3 // Qr a y})
      ≤ 17 * (Nat.card {z : P3 // IsConj zK z} * KZ + Nat.card {z : P3 // IsConj (zK ^ 3) z} * KZ3) :=
        Nat.mul_le_mul_left _ h
    _ = Nat.card {z : P3 // IsConj zK z} * 17 * KZ +
        Nat.card {z : P3 // IsConj (zK ^ 3) z} * 17 * KZ3 := by ring
    _ ≤ 4030387200 * KZ + 4030387200 * KZ3 :=
        Nat.add_le_add (Nat.mul_le_mul_right _ c1) (Nat.mul_le_mul_right _ c3)
    _ = 4030387200 * (KZ + KZ3) := by ring

theorem card_qr {a : P3} (ha : orderOf a = 2) {j : P3} (hj : orderOf j = 17) :
    Nat.card {x : P3 // IsConj a x ∧ Qr x (x⁻¹ * j)} =
      Nat.card {x : P3 // IsConj a x ∧ TestG (x : Equiv.Perm (Fin 8330)) j} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  refine and_congr_right fun hx => ?_
  have hx2 : orderOf x = 2 := by rw [orderOf_of_isConj hx, ha]
  rw [qr_iff hx2 hj, testG_coe]

theorem partners_of (hsA : ∀ g < 7, ∀ r < 8, PHeCn.scA g r = true)
    (hsA3 : ∀ g < 7, ∀ r < 8, PHeCn.scA3 g r = true) :
    countPair PairHe.bs 7 PairHe.wA PairHe.conds heBlocks ≤ 322560 := by
  classical
  have cSzA : PHeT.c = 24990 := Nat.eq_of_beq_eq_true PHeCl.cASz
  have hkA := (ClTP.closNFT_proved (bs := PairHe.bs) (rep := PairHe.wA) He2112.binds He2112.perm
    HeC.ho (by decide) PHeCheck.tabs rfl PHeCheck.hg PHeCheck.repA_eq PHeCheck.okA).2.2
  have hnd := List.nodup_append.1 keys_nodup
  have hndA : ((List.range PHeT.c).map PHeCl.KA).Nodup := by
    rw [← hkA]
    exact hnd.1
  have hvA : ∀ i < PHeT.c, nfValidK 5 HeC.LR (nfX 5 (PHeCl.XA i)) = true := fun i hi =>
    (rec_at PHeCl.recA_all hi (by rw [cSzA] at hi; change i < 49 * 8 * 64; omega)).1
  have clA := card_class_filter (nB := 49) repW_hewA tAMem okA sizeA (cSzA ▸ hkA) (cSzA ▸ hndA)
    PHeCl.recA_all (by norm_num) card_clA
  have hchunk : ∀ {R : Nat} {h : Nat → Nat → Bool} {f V : Nat → Nat},
      (∀ g r, h g r = Nat.beq (f (Nat.add (Nat.mul g 8) r)) (V (Nat.add (Nat.mul g 8) r))) →
      (∀ g < R, ∀ r < 8, h g r = true) → ∀ q < R * 8, f q = V q := by
    intro R h f V hh hall q hq
    have := hall (q / 8) (by omega) (q % 8) (Nat.mod_lt _ (by norm_num))
    rw [hh, split] at this
    exact Nat.eq_of_beq_eq_true this
  have kA : Nat.card {x : P3 // IsConj tAK x ∧ Qr x (x⁻¹ * zK)} = 17 := by
    rw [card_qr (by rw [Subgroup.orderOf_mk]; exact tAOrd) zK_ord]
    refine (clA (fun p => TestG p ((zK : P3) : Equiv.Perm (Fin 8330)))).trans ?_
    exact scan_part (c := PHeT.c) zMem zRep ziRepK hvA
      (hchunk (h := PHeCn.scA) (V := PHeN.SC0) (fun _ _ => rfl) hsA)
      (Nat.eq_of_beq_eq_true PHeCn.sA) (by rw [cSzA]; norm_num)
  have kA3 : Nat.card {x : P3 // IsConj tAK x ∧ Qr x (x⁻¹ * zK ^ 3)} = 17 := by
    rw [card_qr (by rw [Subgroup.orderOf_mk]; exact tAOrd) zK3_ord]
    refine (clA (fun p => TestG p ((zK ^ 3 : P3) : Equiv.Perm (Fin 8330)))).trans ?_
    exact scan_part (c := PHeT.c) (zK ^ 3).2 z3Rep z3iRep hvA
      (hchunk (h := PHeCn.scA3) (V := PHeN.SC1) (fun _ _ => rfl) hsA3)
      (Nat.eq_of_beq_eq_true PHeCn.sA3) (by rw [cSzA]; norm_num)
  have pA := partners_le tAK kA kA3
  rw [card_clA] at pA
  have hpA : Nat.card {y : P3 // Qr tAK y} ≤ 322560 := by omega
  have hP : ∀ x : P3, hePartners x = Nat.card {y : P3 // Qr x y} := fun x =>
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [Qr, ← Subgroup.orderOf_coe, patRel_coe])
  rw [← hePartners_rep repW_hewA tAMem]
  exact (hP tAK).trans_le hpA

theorem countP_fix {A : Array Nat} {f : Nat → Nat} (h : ∀ x < 8330, A[x]! = f x) :
    (List.range 8330).countP (fun i => A[i]! == i) = PHeCn.fixC f := by
  classical
  have hr : (Finset.range 8330).val = (List.range 8330 : Multiset ℕ) := rfl
  have e2 : (List.range 8330).countP (fun i => A[i]! == i) =
      ∑ i ∈ Finset.range 8330, if (A[i]! == i) = true then 1 else 0 := by
    rw [← Finset.card_filter, Finset.card_def, Finset.filter_val, hr, Multiset.filter_coe,
      Multiset.coe_card, List.countP_eq_length_filter]
    simp only [Bool.decide_eq_true]
  rw [PHeCn.fixC, sumN_finset, e2]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Finset.mem_range.1 hi)]
  by_cases hfi : f i = i
  · rw [hfi, Nat.beq_refl]
    simp
  · have hb : Nat.beq (f i) i = false :=
      Bool.eq_false_iff.2 fun h' => hfi (Nat.eq_of_beq_eq_true h')
    rw [hb]
    simp [hfi]

theorem fix_facts : (List.range 8330).countP (fun i => (heGen 0)[i]! == i) = 346 ∧
    (List.range 8330).countP (fun i => PairHe.t1Arr[i]! == i) = 42 := by
  have hf := PHeCn.fix
  unfold PHeCn.fixB at hf
  rw [bAnd_iff] at hf
  refine ⟨?_, ?_⟩
  · rw [countP_fix (f := PHeSn.tAP) fun x hx => ?_, Nat.eq_of_beq_eq_true hf.1]
    rw [tARep x hx]
    exact rep_heGen (k := 0) (by norm_num) ⟨x, hx⟩
  · rw [countP_fix (f := PHeSn.tBP) fun x hx => ?_, Nat.eq_of_beq_eq_true hf.2]
    rw [tBRep x hx]
    exact rep_t1Arr ⟨x, hx⟩

end He

end CertificateChecks.KernelSporSch.PHePart

end
