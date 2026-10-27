module

public import Certificates.Kernel.SporSch.Mathieu.M23OChecks
public import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import CFSG.Certificates.Kernel.SporSch.OddWitSound
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporSpec
public import CFSG.Certificates.Kernel.SporSch.ChainKClassEq
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Th.KernelPlanes
public import CFSG.Sporadic.Th.Local
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporAbs
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Abs
public import CFSG.Sporadic.ThSchreier.AutCore

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23W

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.KS.SporSch.OddWit CFSG.KS.SporSch.M23C3
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M23OC
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 Certificates.Odd87F3 CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem hn : (23 : ℕ) < 2 ^ 32 := by norm_num

theorem hw : (23 : ℕ) < 2 ^ 5 := by norm_num

theorem valid : ValidSchreier m23Certificate := chainK_valid chainQ (by decide) (by decide)

theorem and_of_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem prep_word {wd : List ℤ} {P : ℕ} (h : bAnd(abOK wd, Nat.beq (abWordK 23 5 (mask 5)
    (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1) wd) P) = true) :
    PRep 23 5 P (evalCodes [m23PermA, m23PermB] wd) :=
  prep_of_imageList (img_word (and_of_bAnd h).1 (and_of_bAnd h).2)

abbrev u : Equiv.Perm (Fin 23) := m23InvReps.getD 0 1

theorem pU : PRep 23 5 U u := prep_of_imageList imgRep0

theorem pUi : PRep 23 5 (pinvS 23 5 (mask 5) U) u⁻¹ := (prep_pinvS hw pU).1

theorem beq_mul {P Q R S : ℕ} {a b c d : Equiv.Perm (Fin 23)} (hP : PRep 23 5 P a)
    (hQ : PRep 23 5 Q b) (hR : PRep 23 5 R c) (hS : PRep 23 5 S d)
    (h : Nat.beq (pcomp 23 5 (mask 5) P Q) (pcomp 23 5 (mask 5) R S) = true) : a * b = c * d := by
  rw [beq_pcomp_iff hn (by norm_num) hP hQ hR hS] at h
  exact of_decide_eq_true h

theorem pow_eq_one {P : ℕ} {g : Equiv.Perm (Fin 23)} (hP : PRep 23 5 P g) {e : ℕ}
    (h : Nat.beq (powK 23 5 (mask 5) (pidn 23 5) P e) (pidn 23 5) = true) : g ^ e = 1 := by
  obtain ⟨p1, s1⟩ := prep_powK szOK' hP e
  rw [beq_eq_decide (by norm_num) p1 (prep_pidn (by norm_num) (by norm_num)) s1
    (PF.pidn_shr (by norm_num) (by norm_num))] at h
  exact of_decide_eq_true h

theorem orig_eq : m23Certificate.originalSubgroup =
    Subgroup.closure ({m23PermA, m23PermB} : Set (Equiv.Perm (Fin 23))) := by
  rw [m23Certificate, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem pAc : PRep 23 5 (packL 5 tA) m23PermA := by
  rw [tA_eq]
  exact (prep_packL (by norm_num)).1

theorem pBc : PRep 23 5 (packL 5 tB) m23PermB := by
  rw [tB_eq]
  exact (prep_packL (by norm_num)).1

theorem u_ord : orderOf u = 2 := by
  rw [orderOf_of_ordC pU]
  exact Nat.eq_of_beq_eq_true uOrd

theorem gens_mem : ∀ g ∈ [m23PermA, m23PermB],
    g ∈ Subgroup.closure ({m23PermA, m23PermB} : Set (Equiv.Perm (Fin 23))) := by
  intro g hg
  apply Subgroup.subset_closure
  simpa using hg

theorem word_mem (wd : List ℤ) : evalCodes [m23PermA, m23PermB] wd ∈
    Subgroup.closure ({m23PermA, m23PermB} : Set (Equiv.Perm (Fin 23))) :=
  evalCodes_mem _ gens_mem wd

theorem huK : u ∈ Subgroup.closure ({m23PermA, m23PermB} : Set (Equiv.Perm (Fin 23))) := by
  have e : u = evalCodes [m23PermA, m23PermB] [1] := rfl
  rw [e]
  exact word_mem _

theorem ncard_inv : {z : Equiv.Perm (Fin 23) | z ∈ Subgroup.closure
    ({m23PermA, m23PermB} : Set (Equiv.Perm (Fin 23))) ∧ orderOf z = 2}.ncard = 3795 := by
  have h := card_orderOf_eq hn m23Certificate valid (m := 2) (by norm_num)
  rw [ord2.1] at h
  rw [← h, ← Nat.card_coe_set_eq]
  have e1 : ∀ z, z ∈ m23Certificate.originalSubgroup ↔
      z ∈ Subgroup.closure ({m23PermA, m23PermB} : Set (Equiv.Perm (Fin 23))) := by
    intro z
    rw [orig_eq]
  refine Nat.card_congr ⟨fun z => ⟨⟨z.1, (e1 _).2 z.2.1⟩, ?_⟩,
    fun z => ⟨z.1.1, (e1 _).1 z.1.2, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · rw [Subgroup.orderOf_mk]
    exact z.2.2
  · rw [Subgroup.orderOf_coe]
    exact z.2

theorem inv_mem_class {s : Equiv.Perm (Fin 23)} (hs : s ∈ m23Certificate.originalSubgroup)
    (ho : orderOf s = 2) : s ∈ CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({m23PermA, m23PermB} : Set (Equiv.Perm (Fin 23)))) u := by
  set K := Subgroup.closure ({m23PermA, m23PermB} : Set (Equiv.Perm (Fin 23)))
  obtain ⟨hd, he, -⟩ := clsOK2 0 (by decide)
  have hC := ncard_class hn pAc (prep_pinvS hw pAc).1 pBc (prep_pinvS hw pBc).1 hd he pU
    (by norm_num)
  set C := CFSG.Sporadic.SmallOddCore.conjClass K u
  set I : Set (Equiv.Perm (Fin 23)) := {z | z ∈ K ∧ orderOf z = 2}
  have hCI : C ⊆ I := by
    rintro z ⟨g, hg, rfl⟩
    have hsc : SemiconjBy g u (g * u * g⁻¹) := by simp [SemiconjBy, mul_assoc]
    exact ⟨K.mul_mem (K.mul_mem hg huK) (K.inv_mem hg), (hsc.orderOf_eq).symm.trans u_ord⟩
  have hI : I.ncard = 3795 := ncard_inv
  have e : C = I := Set.eq_of_subset_of_ncard_le hCI (by rw [hI, hC]; rfl) (Set.toFinite _)
  have hsK : s ∈ K := by
    rw [orig_eq] at hs
    exact hs
  rw [e]
  exact ⟨hsK, ho⟩

theorem forall₂_words {ws : List (List ℤ)} {OG : List ℕ} (hl : OG.length = ws.length)
    (h : allN ws.length (fun i => bAnd(abOK (ws.getD i []), Nat.beq (abWordK 23 5 (mask 5)
      (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1) (ws.getD i [])) (OG.getD i 0))) =
        true) :
    List.Forall₂ (PRep 23 5) OG (ws.map (evalCodes [m23PermA, m23PermB])) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
  have hi : i < ws.length := by simpa using h2
  have e1 : OG.get ⟨i, h1⟩ = OG.getD i 0 := by
    rw [List.getD_eq_getElem _ _ h1]
    rfl
  have e2 : (ws.map (evalCodes [m23PermA, m23PermB])).get ⟨i, h2⟩ =
      evalCodes [m23PermA, m23PermB] (ws.getD i []) := by
    rw [List.getD_eq_getElem _ _ hi]
    simp
  rw [e1, e2]
  exact prep_word (allN_spec h i hi)

theorem mem_of_forall₂ {OG : List ℕ} {og : List (Equiv.Perm (Fin 23))}
    (h : List.Forall₂ (PRep 23 5) OG og) {g : Equiv.Perm (Fin 23)} (hg : g ∈ og) :
    ∃ i < OG.length, PRep 23 5 (OG.getD i 0) g := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hl := h.length_eq
  refine ⟨i, hl ▸ hi, ?_⟩
  rw [List.getD_eq_getElem _ _ (hl ▸ hi)]
  exact (List.forall₂_iff_get.1 h).2 i _ hi

theorem rowOK_of (r : Row) {OG : List ℕ} (hr : (r.prime, r.prime ^ r.pexp, OG) ∈ rowsK)
    (hOG : List.Forall₂ (PRep 23 5) OG (r.oddWords.map (evalCodes [m23PermA, m23PermB])))
    (hp : 0 < r.prime) (hodd : r.oddExp % 2 = 1)
    (hcube : 10200960 % r.prime ^ (r.pexp + 1) ≠ 0)
    (hog : ∀ i < OG.length, Nat.beq (pcomp 23 5 (mask 5) U (OG.getD i 0))
      (pcomp 23 5 (mask 5) (OG.getD i 0) U) = true ∧
      Nat.beq (powK 23 5 (mask 5) (pidn 23 5) (OG.getD i 0) r.oddExp) (pidn 23 5) = true) :
    rowOK 23 m23Certificate [m23PermA, m23PermB] u (candAll 23 m23Certificate (toTable u)) r =
      true := by
  have hrep := rep_toTable hn
  have hord : m23Certificate.orderCertificate = 10200960 := checksQ.2
  unfold rowOK
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, hodd⟩, by rw [hord]; exact hcube⟩, fun g hg => ?_⟩, fun T hT => ?_⟩
  · rw [tblEq_eq_iff (Rep.compT (hrep u) (hrep u)) (Rep.idT hn)]
    have h := uSq
    rw [beq_eq_decide (by norm_num) (prep_pcomp hn pU pU) (prep_pidn (by norm_num) (by norm_num))
      (PF.pcomp_shr _ _ hn (by norm_num)) (PF.pidn_shr (by norm_num) (by norm_num))] at h
    exact of_decide_eq_true h
  · obtain ⟨i, hi, pg⟩ := mem_of_forall₂ hOG hg
    obtain ⟨h1, h2⟩ := hog i hi
    rw [commT_eq (hrep u) (hrep g), decide_eq_true_eq,
      powFixW_iff perm_faithful (List.Forall₂.cons (hrep g) List.Forall₂.nil)]
    exact ⟨beq_mul pU pg pg pU h1, by simpa using pow_eq_one pg h2⟩
  · obtain ⟨x, hx, hTx⟩ := exists_of_mem_left_forall₂
      (forall₂_candAllT hn m23Certificate rfl (hrep u)) hT
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff _ valid] at hx
    obtain ⟨hxG, hsq⟩ := hx
    rw [Bool.or_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
      ordTest_iff perm_faithful hTx hp]
    by_cases hxo : orderOf x = r.prime
    · right
      have hcand : u * x = 1 ∨ u * x ∈ CFSG.Sporadic.SmallOddCore.conjClass
          (Subgroup.closure ({m23PermA, m23PermB} : Set (Equiv.Perm (Fin 23)))) u := by
        by_cases h1 : u * x = 1
        · exact Or.inl h1
        · right
          have huG : u ∈ m23Certificate.originalSubgroup := by rw [orig_eq]; exact huK
          refine inv_mem_class (m23Certificate.originalSubgroup.mul_mem huG hxG) ?_
          exact orderOf_eq_prime (by rw [pow_two]; exact hsq) h1
      obtain ⟨hd, he, -⟩ := clsOK2 0 (by decide)
      obtain ⟨X, pX, hX⟩ := rowsPK_of_invCandK hn pAc (prep_pinvS hw pAc).1 pBc
        (prep_pinvS hw pBc).1 hd he pU pUi f3 hcand
      exact witnessOK_of_witPK szOK' hOG pX hTx (witPK_of_rowsPK pX hX hr hxo)
    · exact Or.inl hxo

theorem hog3 : ∀ i < OG3.length, Nat.beq (pcomp 23 5 (mask 5) U (OG3.getD i 0))
    (pcomp 23 5 (mask 5) (OG3.getD i 0) U) = true ∧
    Nat.beq (powK 23 5 (mask 5) (pidn 23 5) (OG3.getD i 0) 3) (pidn 23 5) = true := fun i hi =>
  ⟨allN_spec ogComm.1 i hi, allN_spec ogPow.1 i hi⟩

theorem hog5 : ∀ i < OG5.length, Nat.beq (pcomp 23 5 (mask 5) U (OG5.getD i 0))
    (pcomp 23 5 (mask 5) (OG5.getD i 0) U) = true ∧
    Nat.beq (powK 23 5 (mask 5) (pidn 23 5) (OG5.getD i 0) 21) (pidn 23 5) = true := fun i hi =>
  ⟨allN_spec ogComm.2 i hi, allN_spec ogPow.2 i hi⟩

theorem f3OK : Certificates.Odd87F3.M23.m23F3OK = true := by
  unfold Certificates.Odd87F3.M23.m23F3OK rowsOK
  simp only [Certificates.Odd87F3.M23.rows, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  have e0 : ∀ i < (0 : ℕ), Nat.beq (pcomp 23 5 (mask 5) U (([] : List ℕ).getD i 0))
      (pcomp 23 5 (mask 5) (([] : List ℕ).getD i 0) U) = true ∧
      Nat.beq (powK 23 5 (mask 5) (pidn 23 5) (([] : List ℕ).getD i 0) 1) (pidn 23 5) = true :=
    fun i hi => absurd hi (Nat.not_lt_zero i)
  exact ⟨rowOK_of ⟨3, 2, 3, _⟩ (OG := OG3) (by decide) (forall₂_words rfl bOG3) (by norm_num)
    (by norm_num) (by norm_num) hog3, rowOK_of ⟨5, 1, 21, _⟩ (OG := OG5) (by decide)
    (forall₂_words rfl bOG5) (by norm_num) (by norm_num) (by norm_num) hog5,
    rowOK_of ⟨7, 1, 1, []⟩ (OG := []) (by decide) .nil (by norm_num) (by norm_num) (by norm_num)
      e0, rowOK_of ⟨11, 1, 1, []⟩ (OG := []) (by decide) .nil (by norm_num) (by norm_num)
      (by norm_num) e0, rowOK_of ⟨23, 1, 1, []⟩ (OG := []) (by decide) .nil (by norm_num)
      (by norm_num) (by norm_num) e0⟩

abbrev a0 : Equiv.Perm (Fin 23) := evalCodes [m23PermA, m23PermB] Certificates.CF67.M23.wa

abbrev b0 : Equiv.Perm (Fin 23) := evalCodes [m23PermA, m23PermB] Certificates.CF67.M23.wb

theorem pA0 : PRep 23 5 A0 a0 := prep_word bA0

theorem pB0 : PRep 23 5 B0 b0 := prep_word bB0

abbrev hGens : List (Equiv.Perm (Fin 23)) := c3Words.map (evalCodes [m23PermA, m23PermB])

theorem chainH : ChainK 23 5 hGens c3ChainWords (#v[3, 5] : Vector (Fin 23) 2)
    M23CH.S M23CH.SI M23CH.LR M23CH.TR M23CH.TRI 5 M23CH.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M23CH.head, M23CH.hl,
    by norm_num, M23CH.hs⟩
  have hj3 : j < 3 := by simpa [hGens, c3Words] using hj
  rw [getD_map_eval]
  have h := allN_spec bH j hj3
  exact img_word (and_of_bAnd h).1 (and_of_bAnd h).2

abbrev HQ : RawSchreierDatum 23 := certificate (by decide) hGens c3ChainWords #v[3, 5] (by decide)

theorem H_le : HQ.originalSubgroup ≤
    m23Certificate.originalSubgroup ⊓ Subgroup.centralizer ({a0} : Set (Equiv.Perm (Fin 23))) := by
  rw [certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ hGens := hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  have hj3 : j < 3 := by simpa [hGens, c3Words] using hj
  have pg : PRep 23 5 (M23CH.S j) hGens[j] := by
    have := prep_of_imageList (chainH.2.2.2.1 j hj)
    rwa [List.getD_eq_getElem _ _ hj] at this
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 (beq_mul pg pA0 pA0 pg
    (allN_spec hComm j hj3))⟩
  rw [orig_eq, List.getElem_map]
  exact word_mem _

theorem card_H : Nat.card HQ.originalSubgroup = 180 :=
  (card_group chainH (by decide) (by decide)).trans (Nat.eq_of_beq_eq_true hOrd)

theorem card_C : Nat.card ↥(m23Certificate.originalSubgroup ⊓
    Subgroup.centralizer ({a0} : Set (Equiv.Perm (Fin 23)))) = 180 :=
  (card_centralizer_eq chainQ (by decide) (by decide) (by norm_num) pA0).trans
    (Nat.eq_of_beq_eq_true cent)

theorem H_eq : HQ.originalSubgroup =
    m23Certificate.originalSubgroup ⊓ Subgroup.centralizer ({a0} : Set (Equiv.Perm (Fin 23))) :=
  Subgroup.eq_of_le_of_card_ge H_le (by rw [card_H, card_C])

theorem canon_ne {P Q : ℕ} {g h : Equiv.Perm (Fin 23)} (hP : PRep 23 5 P g) (hQ : PRep 23 5 Q h)
    (sP : P >>> (23 * 5) = 0) (sQ : Q >>> (23 * 5) = 0) (hne : (Nat.beq P Q).not = true) :
    g ≠ h := by
  rw [beq_eq_decide (by norm_num) hP hQ sP sQ] at hne
  simpa using hne

theorem cf67 : Certificates.CF67.M23.m23CF67OK = true := by
  have hrep := rep_toTable hn
  have sA : A0 >>> (23 * 5) = 0 := Nat.eq_of_beq_eq_true abShr.1
  have sB : B0 >>> (23 * 5) = 0 := Nat.eq_of_beq_eq_true abShr.2
  have sId : pidn 23 5 >>> (23 * 5) = 0 := PF.pidn_shr (by norm_num) (by norm_num)
  have pId : PRep 23 5 (pidn 23 5) 1 := prep_pidn (by norm_num) (by norm_num)
  obtain ⟨f1, f2, f3, f4, f5⟩ := abFacts
  unfold Certificates.CF67.M23.m23CF67OK Certificates.CF67.cf67OK Certificates.CF67.cf67OKT
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, fun i hi => ?_⟩, ?_⟩, fun T hT => ?_⟩
  · rw [powFixW_iff perm_faithful (List.Forall₂.cons (hrep a0) List.Forall₂.nil)]
    simpa using pow_eq_one pA0 f1
  · rw [powFixW_iff perm_faithful (List.Forall₂.cons (hrep b0) List.Forall₂.nil)]
    simpa using pow_eq_one pB0 f2
  · rw [commT_eq (hrep a0) (hrep b0), decide_eq_true_eq]
    exact beq_mul pA0 pB0 pB0 pA0 f3
  · cases h : tblEq 23 (toTable a0) (idT 23)
    · rfl
    · exact absurd ((tblEq_eq_iff (hrep a0) (Rep.idT hn)).1 h) (canon_ne pA0 pId sA sId f4)
  · cases h : tblEq 23 (toTable b0) (Certificates.CF67.cf67PowT 23 (toTable a0) i)
    · rfl
    · obtain ⟨p1, s1⟩ := prep_powK szOK' pA0 i
      exact absurd ((tblEq_eq_iff (hrep b0) (rep_powT hn (hrep a0) i)).1 h)
        (canon_ne pB0 p1 sB s1 (allN_spec f5 i hi))
  · rw [checksQ.2]
    decide
  · obtain ⟨g, hg, hTg⟩ := exists_of_mem_left_forall₂
      (forall₂_commAllT hn m23Certificate rfl (hrep a0) (hrep b0)) hT
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff _ valid] at hg
    obtain ⟨hgG, hga, hgb⟩ := hg
    have hgH : g ∈ HQ.originalSubgroup := by
      rw [H_eq]
      exact ⟨hgG, Subgroup.mem_centralizer_singleton_iff.2 hga.symm⟩
    obtain ⟨j, hj, rfl⟩ := (mem_group_iff chainH (by decide) (by decide) _).1 hgH
    have hj' : j < 180 := by
      have := Nat.eq_of_beq_eq_true hOrd
      omega
    have pE := prep_elemK chainH j
    have h := allN_spec elems j hj'
    unfold powCommK at h
    rw [beq_pcomp_iff hn (by norm_num) pE pB0 pB0 pE, decide_eq_true hgb.symm] at h
    rw [powFixW_iff perm_faithful (List.Forall₂.cons hTg List.Forall₂.nil)]
    simpa using pow_eq_one pE (by simpa using h)

end CertificateChecks.KernelSporSch.M23W

end
