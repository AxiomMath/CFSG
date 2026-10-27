module

public import Certificates.Kernel.HN1408.CoverFacts
public import Certificates.Kernel.HN1408.Tr2Facts
public import Certificates.Kernel.HN1408.ClsRFacts
public import Certificates.Kernel.HN1408.SqTChk
public import Certificates.Kernel.HN1408.SqZChk
public import Certificates.Kernel.HN1408.ClsGChk0
public import Certificates.Kernel.HN1408.ClsGChk1
public import Certificates.Kernel.HN1408.ClsGSrt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SqFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux
public import Certificates.Certificate26760
public import Certificates.Certificate26770
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongrK

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.SqZ

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.CzT
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

#kc_forall_chunks g_rep_all (fun s => ClsR.gRep s = true) 28 CFSG.KD.HN1408.ch26774cg.rep 1
#kc_forall_chunks g_srt_all (fun s => ClsR.gSort s = true) 14 CFSG.KD.HN1408.ch26774cg.srt 1
#kc_forall_chunks sq_all (fun s => sqSl s = true) 20 CFSG.KD.HN1408.ch26774sq.sl 1

theorem g_reps : ∀ i < 2800, ∃ c ∈ P1408, RepC (ClsG.R i) (c * elemW g1Word * c⁻¹) := by
  have h0 := ClsR.g_root
  unfold ClsR.rootK at h0
  refine ClsR.reps_memR (P := ClsG.P) (by decide) (Nat.eq_of_beq_eq_true h0)
    (ClsR.repSl_all (len := 100) (ns := 28) (by norm_num) fun s hs => ?_)
  have h := g_rep_all s hs
  unfold ClsR.gRep at h
  exact h

theorem class_g_ge : 30800 ≤ (conjClass P1408 (elemW g1Word)).ncard :=
  ClsR.class_geR (S := ClsG.S) g_reps
    (ClsR.sortSl_all (len := 2200) (ns := 14) (by norm_num) fun s hs => by
      have h := g_srt_all s hs
      unfold ClsR.gSort at h
      exact h)

theorem sqT_ok : Tr2.Tr2OK g1Cent g1Word 720 8 3 SqT.G SqT.T0 SqT.P0 SqT.S SqT.SR SqT.T1 SqT.P1 where
  letters l hl := by
    have hl3 : l < 3 := hl
    interval_cases l <;> decide
  zw := by decide
  head := SqT.sqT_head
  keys := SqT.sqT_keys
  tree := SqT.sqT_tree
  sch := SqT.sqT_sch
  t1 := SqT.sqT_t1

theorem g1_cent (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(P1408 ⊓ centralizer ({elemW g1Word} : Set (Equiv.Perm (Fin 1408)))) = 5760 := by
  have hm := ncard_conjClass_mul_card P1408 (elemW g1Word)
  rw [hP] at hm
  have hcl := class_g_ge
  have hle := Subgroup.card_le_of_le (Tr2.le_cent sqT_ok)
  have hge := Tr2.card_ge sqT_ok
  have hK : Nat.card ↥(P1408 ⊓ centralizer ({elemW g1Word} : Set (Equiv.Perm (Fin 1408)))) ≤
      5760 := by
    by_contra hlt
    have h1 : 30800 * 5761 ≤ (conjClass P1408 (elemW g1Word)).ncard *
        Nat.card ↥(P1408 ⊓ centralizer ({elemW g1Word} : Set (Equiv.Perm (Fin 1408)))) :=
      Nat.mul_le_mul hcl (by omega)
    omega
  omega

@[expose] noncomputable def repS (c : Nat) : Equiv.Perm (Fin 1408) :=
  t0P (fd (R c) 0) * t1P (fd (R c) 1)

theorem named_parts :
    elemA ⟨0, by norm_num⟩ = ⟨45, by norm_num⟩ ∧ elemA ⟨1, by norm_num⟩ = ⟨88, by norm_num⟩ ∧
      elemW g1Word * elemW g1Word = elemA ∧ fd (R 0) 0 < 1280 ∧ fd (R 0) 1 < 24 ∧
      fd (R 1) 0 < 1280 ∧ fd (R 1) 1 < 24 ∧ repS 0 = elemW g1Word ∧
      elemW h2Word * repS 1 = elemW g1Word * elemW h2Word := by
  have h := named_ok
  unfold sqNamedK at h
  simp only [strictB_app] at h
  have hA : RepC (WK wordA) elemA := repC_word (by decide)
  have hG : RepC (WK g1Word) (elemW g1Word) := repC_word (by decide)
  have hH : RepC (WK h2Word) (elemW h2Word) := repC_word (by decide)
  generalize WK wordA = Aa at h hA
  generalize WK g1Word = G1 at h hG
  generalize WK h2Word = H2 at h hH
  unfold repS
  generalize R 0 = r at h ⊢
  generalize R 1 = r' at h ⊢
  obtain ⟨ha0, h⟩ := mkA h
  obtain ⟨ha1, h⟩ := mkA h
  obtain ⟨hsq, h⟩ := mkA h
  obtain ⟨hq, h⟩ := mkA h
  obtain ⟨hq', h⟩ := mkA h
  obtain ⟨hr, h⟩ := mkA h
  obtain ⟨hr', h⟩ := mkA h
  obtain ⟨e0, e1⟩ := mkA h
  have hq1 := Nat.blt_eq.mp hq
  have hq2 := Nat.blt_eq.mp hq'
  have hr1 := Nat.blt_eq.mp hr
  have hr2 := Nat.blt_eq.mp hr'
  have hT0 := repC_pc (t0P_spec hq1).2 (t1P_spec hq2).2
  have hT1 := repC_pc (t0P_spec hr1).2 (t1P_spec hr2).2
  refine ⟨Fin.ext ?_, Fin.ext ?_, ?_, hq1, hq2, hr1, hr2, ?_, ?_⟩
  · rw [← repC_pt hA (by norm_num)]
    exact Nat.eq_of_beq_eq_true ha0
  · rw [← repC_pt hA (by norm_num)]
    exact Nat.eq_of_beq_eq_true ha1
  · have h2 := repC_pc hG hG
    rw [Nat.eq_of_beq_eq_true hsq] at h2
    exact eq_of_repC h2 hA
  · rw [Nat.eq_of_beq_eq_true e0] at hT0
    exact eq_of_repC hT0 hG
  · have h3 := repC_pc hH hT1
    rw [Nat.eq_of_beq_eq_true e1] at h3
    exact eq_of_repC h3 (repC_pc hG hH)

theorem sq_cell_ok {i j : Nat} (hi : i < 1280) (hj : j < 24) :
    sqCellK R (T0 i) (T1 j) (W i) j = true := by
  have hs : i / 64 < 20 := by omega
  have h := sq_all (i / 64) hs
  unfold sqSl at h
  have h' := allN_spec h (i % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h'
  unfold sqRowK at h'
  simp only [strictB_app] at h'
  exact allN_spec h' j hj

theorem conjK_parts {A B c₁ i' j' : Nat} (h : CzInv.conjK R A B c₁ i' j' = true) :
    i' < 1280 ∧ j' < 24 ∧ fd (R (Nat.pred c₁)) 0 < 1280 ∧ fd (R (Nat.pred c₁)) 1 < 24 ∧
      CzInv.cjAt A B (T0 i') (T1 j') (T0 (fd (R (Nat.pred c₁)) 0))
        (T1 (fd (R (Nat.pred c₁)) 1)) 0 = true ∧
      CzInv.cjAt A B (T0 i') (T1 j') (T0 (fd (R (Nat.pred c₁)) 0))
        (T1 (fd (R (Nat.pred c₁)) 1)) 1 = true := by
  unfold CzInv.conjK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, h⟩ := mkA h
  obtain ⟨e, f⟩ := mkA h
  exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.blt_eq.mp c, Nat.blt_eq.mp d, e, f⟩

theorem sq_conj (hP : Nat.card ↥P1408 = 177408000) {g : Equiv.Perm (Fin 1408)}
    (hg : g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) (h2 : g * g = elemA) :
    ∃ c < 2, ∃ h ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))),
      g * h = h * repS c := by
  obtain ⟨ha0, ha1, -⟩ := named_parts
  obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hg
  have hc := sq_cell_ok hi hj
  unfold sqCellK at hc
  simp only [strictB_app] at hc
  have hsq : isBase (pt (T0 i) (pt (T1 j) (pt (T0 i) (pt (T1 j) 0))))
      (pt (T0 i) (pt (T1 j) (pt (T0 i) (pt (T1 j) 1)))) 45 88 = true := by
    unfold isBase
    rw [CzInv.ev_mul hi hj hi hj (by norm_num), CzInv.ev_mul hi hj hi hj (by norm_num), h2, ha0,
      ha1]
    rfl
  rw [hsq] at hc
  rcases mkIf hc with ⟨-, hX⟩ | ⟨hc0, hX⟩
  · exact absurd hX Bool.false_ne_true
  rcases mkIf hX with ⟨-, hX⟩ | ⟨h12, hK⟩
  · exact absurd hX Bool.false_ne_true
  have hc1 : fd (W i) (Nat.mul 3 j) ≠ 0 := fun e => by rw [e] at hc0; exact absurd hc0 (by decide)
  have hc12 : ¬ 2 < fd (W i) (Nat.mul 3 j) := fun e => by
    rw [Nat.blt_eq.mpr e] at h12
    exact absurd h12 (by decide)
  obtain ⟨hi', hj', hq, hq', e0, e1⟩ := conjK_parts hK
  refine ⟨Nat.pred (fd (W i) (Nat.mul 3 j)), by rw [Nat.pred_eq_sub_one]; omega, _,
    CzInv.mem_cz hP hi' hj', ?_⟩
  unfold CzInv.cjAt at e0 e1
  have g0 := Nat.eq_of_beq_eq_true e0
  have g1 := Nat.eq_of_beq_eq_true e1
  rw [CzInv.ev_mul hi hj hi' hj' (by norm_num), CzInv.ev_mul hi' hj' hq hq' (by norm_num)] at g0
  rw [CzInv.ev_mul hi hj hi' hj' (by norm_num), CzInv.ev_mul hi' hj' hq hq' (by norm_num)] at g1
  exact eq_of_base hP (mul_mem hg (CzInv.mem_cz hP hi' hj')) (mul_mem (CzInv.mem_cz hP hi' hj')
    (CzInv.mem_cz hP hq hq')) (Fin.ext g0) (Fin.ext g1)

theorem conj_into_of_odd_index_four {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (hK : ¬ 2 ∣ K.index) (x : G) (hx : x ^ 4 = 1) : ∃ g : G, g * x * g⁻¹ ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T0⟩ : Nonempty (Sylow 2 K) := inferInstance
  set T : Subgroup G := (T0 : Subgroup K).map K.subtype with hTdef
  have hTp : IsPGroup 2 T := T0.isPGroup'.map K.subtype
  have hTidx : ¬ 2 ∣ T.index := by
    have h1 := Subgroup.card_mul_index T
    have h2 := Subgroup.card_mul_index (T0 : Subgroup K)
    have h3 := Subgroup.card_mul_index K
    have hc : Nat.card T = Nat.card (T0 : Subgroup K) :=
      Subgroup.card_map_of_injective K.subtype_injective
    have e : Nat.card T * T.index = Nat.card T * ((T0 : Subgroup K).index * K.index) := by
      rw [h1, hc, ← mul_assoc, h2, h3]
    rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos e]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · exact T0.not_dvd_index h
    · exact hK h
  let TS : Sylow 2 G := hTp.toSylow hTidx
  have hXp : IsPGroup 2 (Subgroup.zpowers x) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (by simpa using hx) : orderOf x ∣ 2 ^ 2)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hXp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q TS
  refine ⟨g, ?_⟩
  have hmem : g * x * g⁻¹ ∈ (TS : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    have hm := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup G)
      (hQ (Subgroup.mem_zpowers x))
    rwa [MulAut.smul_def, MulAut.conj_apply] at hm
  have e : (TS : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  rw [e, hTdef] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  rw [← hy]
  exact y.2

theorem conj_into_cz_four (hP : Nat.card ↥P1408 = 177408000) {x : Equiv.Perm (Fin 1408)}
    (hxP : x ∈ P1408) (hx : x ^ 4 = 1) :
    ∃ c ∈ P1408, c * x * c⁻¹ ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  set K : Subgroup ↥P1408 :=
    (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))).subgroupOf P1408 with hKdef
  have hKc : Nat.card K = 30720 := by
    rw [hKdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
      ← (czT_eq hP).1]
    exact (czT_eq hP).2
  have hKi : K.index = 5775 := by
    have h := Subgroup.card_mul_index K
    rw [hKc, hP] at h
    omega
  have hfin : Finite ↥P1408 := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  obtain ⟨g, hg⟩ := conj_into_of_odd_index_four K (by rw [hKi]; decide) ⟨x, hxP⟩
    (Subtype.ext (by simpa using hx))
  refine ⟨g, g.2, ?_⟩
  rw [hKdef, Subgroup.mem_subgroupOf] at hg
  exact hg

theorem conj_g1 (hP : Nat.card ↥P1408 = 177408000) {x : Equiv.Perm (Fin 1408)}
    (hxP : x ∈ P1408) (hx : x * x = elemA) : ∃ c ∈ P1408, x = c * elemW g1Word * c⁻¹ := by
  obtain ⟨-, -, -, hq, hq', hr, hr', e0, e1⟩ := named_parts
  have h4 : x ^ 4 = 1 := by
    calc x ^ 4 = x ^ 2 * x ^ 2 := by rw [← pow_add]
      _ = (x * x) * (x * x) := by rw [pow_two]
      _ = 1 := by rw [hx, elemA_mul_self]
  obtain ⟨c, hcP, hcz⟩ := conj_into_cz_four hP hxP h4
  have h2 : c * x * c⁻¹ * (c * x * c⁻¹) = elemA := by
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = elemA * c * c⁻¹ := by rw [hx, ← elemA_comm hcP]
      _ = elemA := by group
  obtain ⟨k, hk, h, hh, e⟩ := sq_conj hP hcz h2
  have hhP : h ∈ P1408 := (Subgroup.mem_inf.1 hh).1
  have e' : x = (c⁻¹ * h) * repS k * (c⁻¹ * h)⁻¹ := by
    calc x = c⁻¹ * (c * x * c⁻¹ * h) * h⁻¹ * c := by group
      _ = c⁻¹ * (h * repS k) * h⁻¹ * c := by rw [e]
      _ = _ := by group
  have hch : c⁻¹ * h ∈ P1408 := mul_mem (inv_mem hcP) hhP
  interval_cases k
  · exact ⟨_, hch, by rw [e', e0]⟩
  · have e2 : repS 1 = (elemW h2Word)⁻¹ * elemW g1Word * elemW h2Word := by
      rw [mul_assoc, ← e1]
      group
    refine ⟨(c⁻¹ * h) * (elemW h2Word)⁻¹, mul_mem hch (inv_mem (elemW_mem _)), ?_⟩
    rw [e', e2]
    group

theorem card_cent_eq_of_isConj {x y : ↥P1408} (h : IsConj x y) :
    Nat.card ↥(centralizer ({y} : Set ↥P1408)) = Nat.card ↥(centralizer ({x} : Set ↥P1408)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (Nat.card_congr (TwoHSData.centralizerMulEquiv (MulAut.conj c) x).toEquiv).symm

theorem sq_facts (hP : Nat.card ↥P1408 = 177408000) : SqFacts := by
  obtain ⟨-, -, hsq, -⟩ := named_parts
  let G1 : ↥P1408 := ⟨elemW g1Word, elemW_mem _⟩
  have hconj : ∀ {g : ↥P1408}, g ^ 2 = pA → IsConj G1 g := by
    intro g hg
    have hgg : (g : Equiv.Perm (Fin 1408)) * g = elemA := by
      have := congrArg Subtype.val hg
      simpa [pow_two, coe_pA] using this
    obtain ⟨c, hcP, hc⟩ := conj_g1 hP g.2 hgg
    refine (isConj_subtype_iff P1408 (elemW_mem _) g.2).2 ⟨c, hcP, ?_⟩
    rw [hc]
  refine ⟨⟨G1, by rw [pow_two]; exact Subtype.ext hsq⟩, fun hg hg' =>
    (hconj hg).symm.trans (hconj hg'), fun {g} hg => ?_⟩
  rw [card_cent_eq_of_isConj (hconj hg), Nat.card_congr (centralizerSubtypeEquiv P1408 G1).toEquiv]
  exact g1_cent hP

end CFSG.KD.HN1408.SqZ

end
