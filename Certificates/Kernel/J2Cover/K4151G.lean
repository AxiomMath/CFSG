module

public import Certificates.Kernel.J2Cover.K4151N
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalFixed
public import CFSG.Certificates.SchreierChainOrderStabilizers
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.J2Cover4151

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.External
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover

theorem countProducts_eq_one {Q : RawSchreierDatum 315} (hQ : ValidSchreier Q)
    {a b : Equiv.Perm (Fin 315)}
    (h : ∀ g ∈ Q.originalSubgroup, g * a = a * g → g * b = b * g → g = 1) :
    countProducts 315 (commAll 315 [toTable a, toTable b]) (levelTables Q) (idT 315) = 1 := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  have hspec := countProducts_spec
    (P := fun y : Equiv.Perm (Fin 315) => y * a = a * y ∧ y * b = b * y)
    (f := commAll 315 [toTable a, toTable b]) (fun T y hT => by
      simp only [commAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      rw [commT_iff hT (rep_toTable hn a), commT_iff hT (rep_toTable hn b)])
    (forall₂_levelTables hn Q) (CFSG.Sporadic.Th.Rep.idT hn)
  simp only [one_mul, List.map_id'] at hspec
  change _ = (enumeration Q).countP _ at hspec
  rw [hspec, List.countP_eq_length_filter]
  have h1 : (1 : Equiv.Perm (Fin 315)) ∈ (enumeration Q).filter
      (fun y => decide (y * a = a * y ∧ y * b = b * y)) :=
    List.mem_filter.2 ⟨(mem_enumeration_iff Q hQ 1).2 (one_mem _), by simp⟩
  have hall : ∀ g ∈ (enumeration Q).filter (fun y => decide (y * a = a * y ∧ y * b = b * y)),
      g ∈ ({1} : Finset (Equiv.Perm (Fin 315))) := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := List.mem_filter.1 hg
    simp only [decide_eq_true_eq] at hg2
    exact Finset.mem_singleton.2 (h g ((mem_enumeration_iff Q hQ g).1 hg1) hg2.1 hg2.2)
  have hle := Finset.card_le_card (s := ((enumeration Q).filter
      (fun y => decide (y * a = a * y ∧ y * b = b * y))).toFinset)
    (t := {1}) fun g hg => hall g (List.mem_toFinset.1 hg)
  rw [List.toFinset_card_of_nodup ((enumeration_nodup Q hQ).filter _), Finset.card_singleton]
    at hle
  have hpos := List.length_pos_of_mem h1
  omega

theorem unpack_get' {p i : Nat} (hi : i < 315) : (unpack 315 9 p)[i]! = pg 9 (mask 9) p i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

@[expose] noncomputable def px : Equiv.Perm (Fin 315) := permOfArr 315 fixDStrong[0]!

@[expose] noncomputable def py : Equiv.Perm (Fin 315) := permOfArr 315 fixDStrong[1]!

theorem fD_ok : rawChainOK 315 (fixDStrong.extract 0 2) fixDStrong
    (([1] : List (Fin 315)).map Fin.val).toArray fixDWords 4 = true := by
  rw [fixDBase_eq]
  exact CertificateChecks.KernelJ2Cover.fD_chain.1

theorem rep_px0 : Rep 315 fixDStrong[0]! px :=
  rep_permOfArr_of_chainOK fD_ok (by rw [CertificateChecks.KernelJ2Cover.fD_binds.2.2.2.1]; omega)

theorem rep_py0 : Rep 315 fixDStrong[1]! py :=
  rep_permOfArr_of_chainOK fD_ok (by rw [CertificateChecks.KernelJ2Cover.fD_binds.2.2.2.1]; omega)

theorem rep_px : Rep 315 (unpack 315 9 (CertificateChecks.KernelJ2Cover.FD.S 0)) px := by
  rw [← CertificateChecks.KernelJ2Cover.fD_S 0 (by omega)]
  exact rep_px0

theorem rep_py : Rep 315 (unpack 315 9 (CertificateChecks.KernelJ2Cover.FD.S 1)) py := by
  rw [← CertificateChecks.KernelJ2Cover.fD_S 1 (by omega)]
  exact rep_py0

theorem tblX_eq : tblX = toTable px := by
  unfold tblX
  exact (toTable_eq_arrTable rep_px0).symm

theorem tblY_eq : tblY = toTable py := by
  unfold tblY
  exact (toTable_eq_arrTable rep_py0).symm

theorem word_rep {g : Equiv.Perm (Fin 315)} (hgx : g * px = px * g) (hgy : g * py = py * g) :
    ∀ ws : List Nat, (∀ Z ∈ ws, Z = CertificateChecks.KernelJ2Cover.FD.S 0 ∨
      Z = CertificateChecks.KernelJ2Cover.FD.S 1) →
    ∃ v, Rep 315 (unpack 315 9 (prodK 315 9 ws)) v ∧ g * v = v * g ∧ CnN 315 9 (prodK 315 9 ws)
  | [], _ => by
    have e : unpack 315 9 (prodK 315 9 []) = idA 315 := idK_sound (by quickRfl)
    refine ⟨1, ?_, by rw [one_mul, mul_one], by quickRfl⟩
    rw [e]
    exact rep_idA
  | Z :: ws, h => by
    obtain ⟨v, hv, hgv, cv⟩ := word_rep hgx hgy ws fun Z' hZ' => h Z' (List.mem_cons_of_mem _ hZ')
    obtain ⟨z, hz, hgz, cz⟩ : ∃ z, Rep 315 (unpack 315 9 Z) z ∧ g * z = z * g ∧ CnN 315 9 Z := by
      rcases h Z (by simp) with rfl | rfl
      · exact ⟨px, rep_px, hgx, by quickRfl⟩
      · exact ⟨py, rep_py, hgy, by quickRfl⟩
    refine ⟨z * v, ?_, ?_, canon_pcN cz cv⟩
    · change Rep 315 (unpack 315 9 (pcomp 315 9 (mask 9) Z (prodK 315 9 ws))) (z * v)
      rw [← compA_unpackN cz cv]
      exact rep_compA hz hv
    · rw [← mul_assoc, hgz, mul_assoc, hgv, mul_assoc]

theorem d0K_spec {X V : Nat} (h : CertificateChecks.KernelJ2Cover.d0K X V = true) :
    pg 9 (mask 9) X 0 = 0 ∧ pg 9 (mask 9) V 0 = 0 ∧
      ∀ i < 315, pg 9 (mask 9) X i = i → pg 9 (mask 9) V i = i → i = 0 := by
  unfold CertificateChecks.KernelJ2Cover.d0K at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, fun i hi hx hv => ?_⟩
  have hi' := allN_spec h3 i hi
  rw [hx, hv, Nat.beq_refl] at hi'
  cases h0 : Nat.beq i 0
  · rw [h0] at hi'
    exact absurd hi' Bool.false_ne_true
  · exact Nat.eq_of_beq_eq_true h0

theorem rep_apply {X : Nat} {u : Equiv.Perm (Fin 315)} (hu : Rep 315 (unpack 315 9 X) u)
    (i : Fin 315) : ((u i : Fin 315) : Nat) = pg 9 (mask 9) X i := by
  rw [← hu i, unpack_get' i.2]

theorem fix_zero {g : Equiv.Perm (Fin 315)} (hgx : g * px = px * g) (hgy : g * py = py * g) :
    g 0 = 0 := by
  obtain ⟨v, hv, hgv, -⟩ := word_rep hgx hgy CertificateChecks.KernelJ2Cover.wordV (by
    intro Z hZ
    simp only [CertificateChecks.KernelJ2Cover.wordV, List.mem_cons, List.not_mem_nil,
      or_false] at hZ
    rcases hZ with h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h])
  obtain ⟨hX0, hV0, hall⟩ := d0K_spec CertificateChecks.KernelJ2Cover.d0
  have hx0 : px 0 = 0 := Fin.ext (by rw [rep_apply rep_px]; exact hX0)
  have hv0 : v 0 = 0 := Fin.ext (by rw [rep_apply hv]; exact hV0)
  have hxa : px (g 0) = g 0 := by
    rw [← Equiv.Perm.mul_apply, ← hgx, Equiv.Perm.mul_apply, hx0]
  have hva : v (g 0) = g 0 := by
    rw [← Equiv.Perm.mul_apply, ← hgv, Equiv.Perm.mul_apply, hv0]
  refine Fin.ext (hall _ (g 0).2 ?_ ?_)
  · rw [← rep_apply rep_px, hxa]
  · rw [← rep_apply hv, hva]

@[expose] noncomputable def chainP0 : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) CertificateChecks.KernelJ2Cover.subStrong 5
    (Nat.le_of_eq CertificateChecks.KernelJ2Cover.sb_binds.2.2.2.1.symm) [4, 3] (by decide)
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 5 CertificateChecks.KernelJ2Cover.nilD4151)

theorem subBase_eq : (([4, 3] : List (Fin 315)).map Fin.val).toArray =
    CertificateChecks.KernelJ2Cover.subBase := rfl

theorem chainP0_ok : rawChainOK 315 (CertificateChecks.KernelJ2Cover.subStrong.extract 0 5)
    CertificateChecks.KernelJ2Cover.subStrong (([4, 3] : List (Fin 315)).map Fin.val).toArray
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 5 CertificateChecks.KernelJ2Cover.nilD4151) 4 =
      true := by
  rw [subBase_eq]
  exact CertificateChecks.KernelJ2Cover.sbChain.1

theorem chainP0_valid : ValidSchreier chainP0 := ofArrays_valid (by norm_num) chainP0_ok

theorem levelTables_chainP0 :
    levelTables chainP0 = chainTables 315 CertificateChecks.KernelJ2Cover.subStrong
      CertificateChecks.KernelJ2Cover.subBase := by
  rw [chainP0, ofArrays_levelTables chainP0_ok, subBase_eq]

theorem autChain_ok' : rawChainOK 315 (autStrong.extract 0 2) autStrong
    (([0, 4, 3] : List (Fin 315)).map Fin.val).toArray autWords 4 = true := by
  rw [autBase_eq]
  exact CertificateChecks.KernelJ2Cover.autChain.1

theorem autChain_valid' : ValidSchreier autChain := ofArrays_valid (by norm_num) autChain_ok'

theorem levelTables_autChain' : levelTables autChain = chainTables 315 autStrong autBase := by
  rw [autChain, ofArrays_levelTables autChain_ok', autBase_eq]

theorem subStrong_get {i : Nat} (hi : i < 5) :
    CertificateChecks.KernelJ2Cover.subStrong[i]! = autStrong[i + 2]! := by
  unfold CertificateChecks.KernelJ2Cover.subStrong
  rw [getElem!_pos _ i (by simp [autStrong_size]; omega),
    getElem!_pos autStrong (i + 2) (by rw [autStrong_size]; omega), Array.getElem_extract]
  simp only [Nat.add_comm]

theorem mem_chainP0 {g : Equiv.Perm (Fin 315)} (hg : g ∈ autChain.originalSubgroup)
    (h0 : g 0 = 0) : g ∈ chainP0.originalSubgroup := by
  have hbase : autChain.base.toList = [0, 4, 3] := RawSchreierDatum.ofArrays_base_toList
  have hl : g ∈ autChain.levelSubgroup 1 := by
    refine (autChain.mem_levelSubgroup_iff autChain_valid' 1 (by decide) g).2 ⟨hg, ?_⟩
    rw [hbase]
    intro b hb
    simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hb
    rw [hb]
    exact h0
  refine (Subgroup.closure_le _).2 ?_ hl
  intro s hs
  obtain ⟨hs1, hs2⟩ := (autChain.mem_levelGenerators_iff 1 s).1 hs
  have hs0 : s 0 = 0 := hs2 0 (by rw [hbase]; simp)
  change s ∈ (Vector.ofFn fun j : Fin autStrong.size => permOfArr 315 autStrong[(j : ℕ)]!).toList
    at hs1
  rw [Vector.toList_ofFn, List.mem_ofFn] at hs1
  obtain ⟨⟨j, hj⟩, rfl⟩ := hs1
  rw [autStrong_size] at hj
  rw [chainP0, ofArrays_originalSubgroup]
  by_cases hj2 : 2 ≤ j
  · refine Subgroup.subset_closure ⟨j - 2, by omega, ?_⟩
    rw [subStrong_get (by omega), Nat.sub_add_cancel hj2]
  · exfalso
    have hrep := rep_permOfArr_of_chainOK autChain_ok' (j := j) (by rw [autStrong_size]; omega)
    have hv : (autStrong[j]!)[0]! = 0 := by
      have := hrep 0
      simp only at hs0
      rw [hs0] at this
      simpa using this
    interval_cases j
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)

theorem eq_one {g : Equiv.Perm (Fin 315)} (hg : g ∈ autChain.originalSubgroup)
    (hgx : g * px = px * g) (hgy : g * py = py * g) : g = 1 := by
  have hc : countProducts 315 (commAll 315 [toTable px, toTable py]) (levelTables chainP0)
      (idT 315) = 1 := by
    rw [← tblX_eq, ← tblY_eq, levelTables_chainP0]
    exact CertificateChecks.KernelJ2Cover.countSB
  exact eq_one_of_countProducts chainP0_valid hc (mem_chainP0 hg (fix_zero hgx hgy)) hgx hgy

theorem centPD : countProducts 315 (commAll 315 [tblX, tblY]) (chainTables 315 autStrong autBase)
    (idT 315) = 1 := by
  rw [tblX_eq, tblY_eq, ← levelTables_autChain']
  exact countProducts_eq_one autChain_valid' fun g hg hgx hgy => eq_one hg hgx hgy

end CertificateChecks.J2Cover4151

end
