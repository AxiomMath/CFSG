module

public import Certificates.Kernel.Misc.Perm.HS100.SpOrb
public import Certificates.Kernel.Misc.Perm.HS100.SpOrbK
public import Certificates.Kernel.Misc.Perm.HS100.SpStab
public import Certificates.Kernel.Misc.Perm.HS100.NGlue
public import CFSG.Certificates.Kernel.RightOrbBitsSound
import CFSG.Certificates.Kernel.Spor.PackFld

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Sp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open CFSG.KC.Misc.ArrEnum (permB pp_of_permB memK anyNP_eq)
open CFSG.KC.PermWit (siftR cntK)
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP and_of card_filter_fin)
open CertificateChecks.KernelMisc.HS100.S0 (e0_get e0Pin listOf any_eq cE0 cK cK_eq Z0 ppZ)
open CertificateChecks.KernelMisc.HS100.N (n_get nPin cNN mem_e0 zasConj_unpack pZ)

theorem allN_eq_all {n : ℕ} {f : ℕ → Bool} : allN n f = (List.range n).all f := by
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    exact allN_spec h i (List.mem_range.1 hi)
  · intro h
    exact CFSG.KS.PackFld.allN_of_forall fun i hi => h i (List.mem_range.2 hi)

theorem allLt_eq_allN {n : ℕ} {f : ℕ → Bool} : allLt n f = allN n f := by
  apply Bool.eq_iff_iff.2
  rw [allLt_iff]
  constructor
  · intro h
    exact CFSG.KS.PackFld.allN_of_forall h
  · intro h i hi
    exact allN_spec h i hi

theorem ppN {k : ℕ} (hk : k < 2) : PP 100 7 (N.NX.F k) := pp_of_permB sz (N.perms'.1 k hk)

theorem ppE' {i : ℕ} (hi : i < 16) : canonK 100 7 (mask 7) (100 * 7) (S0.E0.T i) = true := by
  have h := cE0
  rw [S0.nums'.2.2.2.2.2.2.2.2.2.2.2.1] at h
  exact h i hi

theorem e0List : zasE0Cert.pts.toList = (List.range 16).map fun i => unpack 100 7 (S0.E0.T i) := by
  rw [listOf e0Pin.2, S0.nums'.2.2.2.2.2.2.2.2.2.2.2.1]

theorem nList : zasNCert.pts.toList = (List.range 11520).map fun i => unpack 100 7 (N.NN.T i) := by
  rw [listOf nPin, N.nums'.2.1]

theorem z_eq : s5Z = unpack 100 7 Z0 := S0.z0_eq

theorem pg_lt {p i : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true) (hi : i < 100) :
    pg 7 (mask 7) p i < 100 := by
  unfold canonK at hp
  rw [bAnd_iff, bAnd_iff] at hp
  exact Nat.blt_eq.mp (allN_spec hp.2.2 i hi)

theorem sift' : (∀ k < 2, siftR 100 7 C.LR C.TRI C.BP 5 (N.NX.F k) = true) ∧
    ∀ k < 4, siftR 100 7 C.LR C.TRI C.BP 5 (S0.EX.F k) = true :=
  ⟨fun k hk => allN_spec (and_of sift).1 k hk, fun k hk => allN_spec (and_of sift).2 k hk⟩

theorem zasConjInv_unpack {p q : ℕ} (hp : PP 100 7 p) (hq : canonK 100 7 (mask 7) (100 * 7) q = true) :
    zasConjInv (unpack 100 7 p) (unpack 100 7 q) = unpack 100 7 (pZI p q) := by
  rw [zasConjInv, invCand_PP hp, compA_unpack hp.inv.1 hq,
    compA_unpack (canonK_pcomp hp.inv.1 hq) hp.1]
  rfl

theorem pZI_canon {p q : ℕ} (hp : PP 100 7 p) (hq : canonK 100 7 (mask 7) (100 * 7) q = true) :
    canonK 100 7 (mask 7) (100 * 7) (pZI p q) = true :=
  canonK_pcomp (canonK_pcomp hp.inv.1 hq) hp.1

theorem pZ_canon {p q : ℕ} (hp : PP 100 7 p) (hq : canonK 100 7 (mask 7) (100 * 7) q = true) :
    canonK 100 7 (mask 7) (100 * 7) (pZ p q) = true :=
  canonK_pcomp (canonK_pcomp hp.1 hq) hp.inv.1

theorem om_get {i : ℕ} (hi : i < 100) : zasOmVec[i]! = cond (omB i) 1 0 := by
  unfold zasOmVec
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have e : (i ∈ [8, 51, 53, 92, 70, 97]) ↔ omB i = true := by
    simp only [omB, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true, Nat.beq_eq,
      or_assoc]
  by_cases h : omB i = true
  · rw [if_pos (e.2 h), h]
    rfl
  · rw [if_neg (fun h' => h (e.1 h')), Bool.eq_false_iff.2 h]
    rfl

theorem om_one {i : ℕ} (hi : i < 100) : (zasOmVec[i]! = 1) ↔ omB i = true := by
  rw [om_get hi]
  cases omB i <;> simp

theorem om' : cntK 100 omB = 6 ∧
    (∀ k < 2, ∀ i < 100, Bool.beq (omB (pg 7 (mask 7) (N.NX.F k) i)) (omB i) = true) ∧
    ∀ i < 16, fixOmK (S0.E0.T i) = true := by
  have h := om
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, fun k hk i hi => allN_spec (allN_spec h2 k hk) i hi, fun i hi => allN_spec h3 i hi⟩

theorem fixesOm_eq {t : ℕ} (_ht : canonK 100 7 (mask 7) (100 * 7) t = true) :
    zasFixesOm (unpack 100 7 t) = fixOmK t := by
  unfold zasFixesOm fixOmK
  rw [allLt_eq_allN]
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    refine CFSG.KS.PackFld.allN_of_forall fun i hi => ?_
    have e := allN_spec h i hi
    rw [unpack_get' hi] at e
    have e2 : (zasOmVec[i]! != 1) = !(omB i) := by
      rw [om_get hi]
      cases omB i <;> rfl
    rw [e2] at e
    simpa [beq_iff_eq, Nat.beq_eq] using e
  · intro h
    refine CFSG.KS.PackFld.allN_of_forall fun i hi => ?_
    have e := allN_spec h i hi
    rw [unpack_get' hi]
    have e2 : (zasOmVec[i]! != 1) = !(omB i) := by
      rw [om_get hi]
      cases omB i <;> rfl
    rw [e2]
    simpa [beq_iff_eq, Nat.beq_eq] using e

theorem gInv_eq {k : ℕ} (hk : k < 2) : zasGInv[k]! = unpack 100 7 (C.SI k) := by
  have h := invEqK_sound (allN_spec cperm k (by omega))
  unfold zasGInv
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn, hs100Arr_eq k (by omega),
    Nat.eq_of_beq_eq_true (allN_spec cFS k (by omega))]
  exact h.1

theorem act_eq : ∀ k < 2, ∀ a, zasSetAct k a = compA 100 a (unpack 100 7 (C.SI k)) := by
  intro k hk a
  unfold zasSetAct
  rw [gInv_eq hk]
  rfl

theorem fixVec_size : zasFixVec.size = 100 := by
  unfold zasFixVec
  exact Array.size_ofFn

theorem root_eq : zasFixVec = CFSG.KC.RightOrbBits.decB 100 (OT 0) := by
  have hr := orbRoot
  have hc : OT 0 < 2 ^ 100 := (CFSG.KC.RightOrbBits.closPtB_spec (allN_spec orbCl 0 (by norm_num))).1
  apply Array.ext (by rw [fixVec_size, CFSG.KC.RightOrbBits.decB_size])
  intro i h1 h2
  have hi : i < 100 := by rw [fixVec_size] at h1; exact h1
  rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, CFSG.KC.RightOrbBits.decB_get hc]
  have e0 := Nat.eq_of_beq_eq_true (allN_spec hr i hi)
  rw [CFSG.KC.RightOrbBits.bitK_eq] at e0
  have e1 : cond (Nat.testBit (OT 0) i) 1 0 =
      cond (allN 16 fun j => Nat.beq (pg 7 (mask 7) (S0.E0.T j) i) i) 1 0 := e0
  rw [e1]
  unfold zasFixVec
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  simp only
  have e : (zasE0Cert.pts.toList.all fun x => x[i]! == i) =
      allN 16 fun j => Nat.beq (pg 7 (mask 7) (S0.E0.T j) i) i := by
    rw [e0List, List.all_map, allN_eq_all]
    refine congrArg (List.all (List.range 16)) (funext fun j => ?_)
    simp only [Function.comp_apply]
    rw [unpack_get' hi]
    exact Bool.eq_iff_iff.2 (by rw [beq_iff_eq, Nat.beq_eq])
  rw [e]
  cases allN 16 fun j => Nat.beq (pg 7 (mask 7) (S0.E0.T j) i) i <;> rfl

theorem valid_dec {c : ℕ} (hc : c < 2 ^ 100) :
    zasSetValid (CFSG.KC.RightOrbBits.decB 100 c) = true := by
  unfold zasSetValid
  rw [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨CFSG.KC.RightOrbBits.decB_size 100 c, fun j _ => ?_⟩
  rw [CFSG.KC.RightOrbBits.decB_get hc]
  cases Nat.testBit c j <;> decide

theorem orbit : arrCertOK zasSetAct 2 zasSetValid zasSetKey zasFixVec zasFCert = true ∧
    zasFCert.pts.size = 3850 := by
  have h := CFSG.KC.RightOrbBits.arrBfs_of_bits (n := 100) (w := 7) (ng := 2) (ngc := 2)
    (N := 3850) (r := 0) (fuel := 2 ^ 14) (G := C.SI) (T := OT) (E := OE) (D := OD) (S := OS)
    (act := zasSetAct) (valid := zasSetValid) (root := zasFixVec)
    (by norm_num) le_rfl act_eq (fun i hi => allN_spec orbCl i hi)
    (fun i hi => allN_spec orbTr i hi) (by norm_num) root_eq
    (fun i hi => valid_dec (CFSG.KC.RightOrbBits.closPtB_spec (allN_spec orbCl i hi)).1) orbKeys
    (by norm_num)
  exact ⟨h.1, h.2.2⟩

theorem zasSpecialOK_true : zasSpecialOK = true := by
  have cZ := ppZ.1
  have hE := fun (i : ℕ) (hi : i < 16) => ppE' hi
  have hEinv := and_of eInv
  have h1 : validA 100 s5Z = true := by
    rw [z_eq]
    exact validA_unpack (and_of S0.zperm).1
  have h3 : (zasE0Cert.pts.size == 16) = true := by
    rw [e0Pin.2, Array.size_ofFn, S0.nums'.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  have h4 : allLt zasE0Gens.size (fun k => s5InP zasE0Gens[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk4 : k < 4 := hk
    rw [e0_get k hk4]
    exact s5InP_unpack (sift'.2 k hk4)
  have h5 : (zasE0Cert.pts.toList.all fun x => eqA 100 (compA 100 x x) (idA 100)) = true := by
    rw [e0List, List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply]
    rw [compA_unpack (hE i hi') (hE i hi'), hidA, eqA_F (canonK_pcomp (hE i hi') (hE i hi')) pidPP.1]
    exact allN_spec hEinv.1 i hi'
  have h6 : (zasE0Cert.pts.toList.all fun x => zasE0Cert.pts.toList.all fun y =>
      eqA 100 (compA 100 x y) (compA 100 y x)) = true := by
    rw [e0List, List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply]
    rw [List.all_map, List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    simp only [Function.comp_apply]
    rw [← commA, cK_eq (hE i hi') (hE j hj')]
    exact allN_spec (allN_spec hEinv.2 i hi') j hj'
  have h7 : zasMem zasE0Cert s5Z = true := by
    rw [z_eq, mem_e0 cZ]
    exact S0.mems'.2.1
  have h8 : enumOK 100 zasNGens zasNKeys zasNCert = true := by
    have hs : zasNGens.size = N.NN.ng := by rw [N.nums'.1]; rfl
    have hg : ∀ k < N.NN.ng, zasNGens[k]! = unpack 100 7 (N.NN.G k) := fun k hk => by
      rw [N.nums'.1] at hk; rw [n_get k hk, N.nums'.2.2 k hk]
    have hp : ∀ k < N.NN.ng, permOK 100 7 (mask 7) (100 * 7) (N.NN.G k)
        (pinvS 100 7 (mask 7) (N.NN.G k)) = true := fun k hk => by
      rw [N.nums'.1] at hk; rw [N.nums'.2.2 k hk]; exact N.perms'.1 k hk
    exact enumOK_of_bfsK_base hs hg hp N.NN.ok (by decide) N.keys (by rw [N.nums'.2.1]; norm_num)
  have h9 : (zasNCert.pts.size == 11520) = true := by
    rw [nPin, Array.size_ofFn, N.nums'.2.1]
    rfl
  have h10 : allLt zasNGens.size (fun k => s5InP zasNGens[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk2 : k < 2 := hk
    rw [n_get k hk2]
    exact s5InP_unpack (sift'.1 k hk2)
  have h11 : allLt zasNGens.size (fun k => zasE0Cert.pts.toList.all fun x =>
      zasMem zasE0Cert (zasConj zasNGens[k]! x) &&
        zasMem zasE0Cert (zasConjInv zasNGens[k]! x)) = true := by
    rw [allLt_iff]
    intro k hk
    have hk2 : k < 2 := hk
    rw [n_get k hk2, e0List, List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply]
    rw [zasConj_unpack (ppN hk2) (hE i hi'), zasConjInv_unpack (ppN hk2) (hE i hi'),
      mem_e0 (pZ_canon (ppN hk2) (hE i hi')), mem_e0 (pZI_canon (ppN hk2) (hE i hi'))]
    exact allN_spec (allN_spec eNorm k hk2) i hi'
  have h12 : (zasE0Cert.pts.toList.all fun e =>
      eqA 100 e (idA 100) || zasNCert.pts.toList.any fun a => eqA 100 (zasConj a s5Z) e) =
      true := by
    rw [e0List, List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply]
    have ht := allN_spec trans i hi'
    rw [Bool.or_eq_true] at ht
    rw [hidA, eqA_F (hE i hi') pidPP.1, Bool.or_eq_true]
    rcases ht with ht | ht
    · exact Or.inl ht
    · right
      rw [Bool.and_eq_true, Nat.blt_eq] at ht
      rw [nList, List.any_map, List.any_eq_true]
      refine ⟨NW i, List.mem_range.2 ht.1, ?_⟩
      simp only [Function.comp_apply]
      have hc := cNN (NW i) (by rw [N.nums'.2.1]; exact ht.1)
      have hpp : PP 100 7 (N.NN.T (NW i)) :=
        pp_of_permB sz (allN_spec N.npPerm (NW i) (by rw [N.nums'.2.1]; exact ht.1))
      rw [z_eq, zasConj_unpack hpp cZ, eqA_F (pZ_canon hpp cZ) (hE i hi')]
      exact ht.2
  have h13 : allLt 2 (fun k => validA 100 (hs100Arr k)) = true := by
    rw [allLt_iff]
    intro k hk
    rw [hs100Arr_eq k (by omega), Nat.eq_of_beq_eq_true (allN_spec cFS k (by omega))]
    have h := invEqK_sound (allN_spec cperm k (by omega))
    unfold validA
    rw [h.1]
    exact h.2
  have h14 : (Finset.univ.filter fun i : Fin 100 => zasOmVec[i.1]! = 1).card = 6 := by
    have e : (Finset.univ.filter fun i : Fin 100 => zasOmVec[i.1]! = 1) =
        Finset.univ.filter fun i : Fin 100 => omB i.1 = true :=
      Finset.filter_congr fun i _ => om_one i.2
    rw [e, card_filter_fin, ← CFSG.KC.PermWit.cntK_eq]
    exact om'.1
  have h15 : allLt zasNGens.size (fun k => allLt 100 fun i =>
      zasOmVec[(zasNGens[k]!)[i]!]! == zasOmVec[i]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk2 : k < 2 := hk
    rw [allLt_iff]
    intro i hi
    rw [n_get k hk2, unpack_get' hi]
    have hlt : pg 7 (mask 7) (N.NX.F k) i < 100 := pg_lt (N.cNX hk2) hi
    rw [om_get hlt, om_get hi]
    have e := om'.2.1 k hk2 i hi
    revert e
    cases omB (pg 7 (mask 7) (N.NX.F k) i) <;> cases omB i <;> decide
  have h16 : (zasE0Cert.pts.toList.all zasFixesOm) = true := by
    rw [e0List, List.all_map, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply]
    rw [fixesOm_eq (hE i hi')]
    exact om'.2.2 i hi'
  have h17 : (zasNCert.pts.toList.all fun x => !zasFixesOm x || zasMem zasE0Cert x) = true := by
    rw [nList, List.all_map, List.all_eq_true]
    intro t ht
    have ht' := List.mem_range.1 ht
    have hc := cNN t (by rw [N.nums'.2.1]; exact ht')
    simp only [Function.comp_apply]
    rw [fixesOm_eq hc, mem_e0 hc]
    exact allN_spec nStab t ht'
  unfold zasSpecialOK
  rw [h1, e0Pin.1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, orbit.1, orbit.2, h14, h15, h16,
    h17]
  rfl

end CertificateChecks.KernelMisc.HS100.Sp

end
