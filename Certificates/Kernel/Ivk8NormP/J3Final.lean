module

public import Certificates.Kernel.Ivk8NormP.J3
public import Certificates.Certificate55105
public import Certificates.Kernel.Sporadic.OddCore.J3PGGlue
public import CFSG.Certificates.Kernel.Ivk8NormPRes
public import CFSG.Certificates.Kernel.Ivk8NormSound
public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
public import CFSG.Certificates.Kernel.Spor.PK.CertBridge
public import CFSG.Certificates.SchreierChainOrder
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12NormP
public import CFSG.Sporadic.SmallOddCore.J3
public import CFSG.Sporadic.Schreier.PairJ3Order
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Norm
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

set_option maxRecDepth 400000

namespace CFSG.KS.Ivk8NormP.J3

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8NormP CFSG.KC.YoshQ CFSG.KC.Ivk8N
  CFSG.KC.Enum CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore CFSG.KD.J3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native CFSG.Certificates
  CFSG.KS.PK Subgroup

@[expose] def wv (σ τ : ℕ → Equiv.Perm (Fin 6156)) : List ℤ → Equiv.Perm (Fin 6156)
  | [] => 1
  | z :: w => (if 0 < z then σ (z.toNat - 1) else τ ((-z).toNat - 1)) * wv σ τ w

theorem prep_evalN {gs gis : List ℕ} {σ τ : ℕ → Equiv.Perm (Fin 6156)}
    (hg : ∀ i, PRep 6156 (gs.getD i (pidn 6156 13)) (σ i))
    (hgi : ∀ i, PRep 6156 (gis.getD i (pidn 6156 13)) (τ i)) :
    ∀ w, PRep 6156 (evalN 6156 13 gs gis w) (wv σ τ w)
  | [] => prep_pidn (by norm_num)
  | z :: w => by
    rw [evalN, wv]
    split_ifs
    · exact prep_pmN (by norm_num) (hg _) (prep_evalN hg hgi w)
    · exact prep_pmN (by norm_num) (hgi _) (prep_evalN hg hgi w)

theorem wv_mem {G : Subgroup (Equiv.Perm (Fin 6156))} {σ τ : ℕ → Equiv.Perm (Fin 6156)}
    (hσ : ∀ i, σ i ∈ G) (hτ : ∀ i, τ i ∈ G) : ∀ w, wv σ τ w ∈ G
  | [] => G.one_mem
  | z :: w => by
    rw [wv]
    split_ifs
    · exact G.mul_mem (hσ _) (wv_mem hσ hτ w)
    · exact G.mul_mem (hτ _) (wv_mem hσ hτ w)

@[expose] noncomputable def sG (i : ℕ) : Equiv.Perm (Fin 6156) :=
  ([j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14].map (tp 6156)).getD i 1

theorem sG_eq0 : sG 0 = tp 6156 (j3CentTbl 10) := by
  simp only [sG, List.map_cons, List.getD_cons_zero]

theorem sG_eq1 : sG 1 = tp 6156 (j3CentTbl 11) := by
  simp only [sG, List.map_cons, List.getD_cons_zero, List.getD_cons_succ]

theorem sG_eq2 : sG 2 = tp 6156 (j3CentTbl 12) := by
  simp only [sG, List.map_cons, List.getD_cons_zero, List.getD_cons_succ]

theorem sG_eq3 : sG 3 = tp 6156 (j3CentTbl 13) := by
  simp only [sG, List.map_cons, List.getD_cons_zero, List.getD_cons_succ]

theorem sG_eq4 : sG 4 = tp 6156 (j3CentTbl 14) := by
  simp only [sG, List.map_cons, List.getD_cons_zero, List.getD_cons_succ]

@[expose] noncomputable def sGi (i : ℕ) : Equiv.Perm (Fin 6156) := (sG i)⁻¹

@[expose] noncomputable def sA (i : ℕ) : Equiv.Perm (Fin 6156) := [j3Gen 0, j3Gen 1].getD i 1

theorem prep_g1 (i : ℕ) : PRep 6156 (g1.getD i (pidn 6156 13)) (sG i) ∧
    PRep 6156 (g1i.getD i (pidn 6156 13)) (sGi i) := by
  rcases i with _ | _ | _ | _ | _ | i <;>
    simp only [g1, g1i, sGi, sG, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, List.getD_nil, inv_one, Nat.reduceAdd]
  · exact prep_cent (by norm_num)
  · exact prep_cent (by norm_num)
  · exact prep_cent (by norm_num)
  · exact prep_cent (by norm_num)
  · exact prep_cent (by norm_num)
  · exact ⟨prep_pidn (by norm_num), prep_pidn (by norm_num)⟩

theorem prep_of_rep {X : ℕ} {g : Equiv.Perm (Fin 6156)}
    (hX : ∀ i : ℕ, (CFSG.KS.Raw.unpack 6156 13 X)[i]! < 2 ^ 32)
    (h : CFSG.Sporadic.Th.Rep (G := Equiv.Perm (Fin 6156)) 6156 (CFSG.KS.MulH.tabT (CFSG.KS.Raw.unpack 6156 13 X)) g) :
    PRep 6156 X g := by
  intro q hq
  have e := h q hq
  rw [CFSG.KS.MulH.ap_tabT _ (hX q)] at e
  rw [← CFSG.KS.Raw.Orb.unpack_get hq, e]
  simp [CFSG.Sporadic.Th.idx, hq]

theorem prep_gen {l : ℕ}
    (hl : l < 2) : PRep 6156 (CertificateChecks.KernelCensus.J3S.F l) (j3Gen l) := by
  have h := j3_groupData.rep l (by interval_cases l <;> simp [j3PGTbls])
  rw [J3W.pg_eq hl] at h
  interval_cases l
  · exact prep_of_rep (fun _ => CFSG.KS.MulH.unpack_lt J3W.cn.2.2.1) h
  · exact prep_of_rep (fun _ => CFSG.KS.MulH.unpack_lt J3W.cn.2.2.2.1) h

theorem prep_gA (i : ℕ) :
    PRep 6156 (gA.getD i (pidn 6156 13)) (sA i) := by
  rcases i with _ | _ | i <;>
    simp only [gA, sA, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
  · exact prep_gen (by norm_num)
  · exact prep_gen (by norm_num)
  · exact prep_pidn (by norm_num)

@[expose] noncomputable def oN (i : ℕ) : ℕ := pg 13 (mask 13) j3O i

theorem oN_facts : ∀ i < 80, oN i < 6156 ∧ (i + 1 = 80 ∨ oN i < oN (i + 1)) := by
  have h := ch5253_j3_sorted
  unfold sortedOK at h
  rw [List.all_eq_true] at h
  intro i hi
  have := h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, beq_iff_eq] at this
  exact this

theorem oN_lt (i : Fin 80) : oN i < 6156 := (oN_facts i i.2).1

theorem oN_strictMono : StrictMono fun i : Fin 80 => oN i := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have hi := i.isLt
  rcases (oN_facts i (by omega)).2 with h | h
  · omega
  · simpa [Fin.val_succ] using h

@[expose] noncomputable def o : Fin 80 ↪ Fin 6156 :=
  ⟨fun i => ⟨oN i, oN_lt i⟩, fun a b h => oN_strictMono.injective (congrArg Fin.val h)⟩

theorem res_spec {X : ℕ} {g : Equiv.Perm (Fin 6156)} (hX : PRep 6156 X g) {σ : VP 80}
    (h : resOK 13 j3O 80 X σ = true) : ∀ i, g (o i) = o (pkp σ i) := by
  intro i
  unfold resOK at h
  rw [List.all_eq_true] at h
  have e := Nat.eq_of_beq_eq_true (h i (List.mem_range.2 i.2))
  apply Fin.ext
  have e1 := hX (oN i) (oN_lt i)
  change (g ⟨oN i, oN_lt i⟩ : ℕ) = oN (pkp σ i)
  rw [← e1, pkp_apply]
  exact e

theorem j3Sig_length : j3Sig.length = 5 := rfl

theorem j3Fr1_length : j3Fr1.length = 3 := rfl

theorem j3Fr2_length : j3Fr2.length = 3 := rfl

@[expose] noncomputable def ρ (g : Equiv.Perm (Fin 6156)) : Equiv.Perm (Fin 80) := by
  classical
  exact if h : g ∈ resStab o then resHom o ⟨g, h⟩ else 1

theorem resHom_eq_ρ {g : Equiv.Perm (Fin 6156)} (hg : g ∈ resStab o) :
    resHom o ⟨g, hg⟩ = ρ g := by
  rw [ρ, dif_pos hg]

theorem ρ_mul {g h : Equiv.Perm (Fin 6156)} (hg : g ∈ resStab o) (hh : h ∈ resStab o) :
    ρ (g * h) = ρ g * ρ h := by
  rw [← resHom_eq_ρ hg, ← resHom_eq_ρ hh, ← resHom_eq_ρ (mul_mem hg hh)]
  exact (resHom o).map_mul ⟨g, hg⟩ ⟨h, hh⟩

theorem ρ_inv {g : Equiv.Perm (Fin 6156)} (hg : g ∈ resStab o) : ρ g⁻¹ = (ρ g)⁻¹ := by
  rw [← resHom_eq_ρ hg, ← resHom_eq_ρ (inv_mem hg)]
  exact (resHom o).map_inv ⟨g, hg⟩

theorem ρ_one : ρ 1 = 1 := by
  rw [← resHom_eq_ρ (one_mem _)]
  exact (resHom o).map_one

theorem res_of {X : ℕ} {g : Equiv.Perm (Fin 6156)} (hX : PRep 6156 X g) {σ : VP 80}
    (h : resOK 13 j3O 80 X σ = true) : g ∈ resStab o ∧ ρ g = pkp σ := by
  have hm := mem_resStab_of (res_spec hX h)
  exact ⟨hm, by rw [← resHom_eq_ρ hm, resHom_eq hm (res_spec hX h)]⟩

theorem res_gen (i : ℕ) : sG i ∈ resStab o ∧ ρ (sG i) = (j3Sig.map pkp).getD i 1 := by
  by_cases hi : i < 5
  · have hr := List.all_eq_true.1 ch5253_j3_res i (List.mem_range.2 hi)
    have hl : i < g1.length := by simpa [g1] using hi
    have e : g1.getD i 0 = g1.getD i (pidn 6156 13) := by
      rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl]
    rw [e] at hr
    obtain ⟨hm, hρ⟩ := res_of (prep_g1 i).1 hr
    refine ⟨hm, ?_⟩
    rw [hρ, ← pkp_oneV, List.getD_map]
  · have h1 : sG i = 1 := by
      rw [sG, List.getD_eq_default _ _ (by simp; omega)]
    have h2 : (j3Sig.map pkp).getD i 1 = 1 := List.getD_eq_default _ _ (by rw [List.length_map, j3Sig_length]; omega)
    rw [h1, h2, ρ_one]
    exact ⟨one_mem _, rfl⟩

theorem res_word {K : Subgroup (Equiv.Perm (Fin 6156))} (hK : K ≤ resStab o)
    (hG : ∀ i, sG i ∈ K) : ∀ w, wv sG sGi w ∈ K ∧ ρ (wv sG sGi w) = evalCodes (j3Sig.map pkp) w
  | [] => ⟨one_mem _, ρ_one⟩
  | z :: w => by
    obtain ⟨hw, hρw⟩ := res_word hK hG w
    rw [wv, evalCodes]
    split_ifs
    · refine ⟨mul_mem (hG _) hw, ?_⟩
      rw [ρ_mul (res_gen _).1 (hK hw), (res_gen _).2, hρw]
    · refine ⟨mul_mem (inv_mem (hG _)) hw, ?_⟩
      rw [sGi, ρ_mul (inv_mem (res_gen _).1) (hK hw), ρ_inv (res_gen _).1, (res_gen _).2, hρw]

theorem prime_dvd_1920 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 1920) : p = 3 ∨ p = 5 := by
  have e : (1920 : ℕ) = 2 ^ 7 * (3 * 5) := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)

theorem ordV_certificate_base {n : ℕ} (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List ℤ)) {k : ℕ} (base : Vector (Fin n) k) (hbase : base.toList.Nodup)
    (Sc : List (VP n)) : ordV Sc (certificate hn gens words base hbase).base = ordV Sc base := rfl

@[expose] noncomputable def Q : CFSG.Certificates.RawSchreierDatum 80 :=
  certificate (by decide) ((j3Kw.map (evV j3Sig)).map pkp) j3Words #v[0, 2] (by decide)

theorem Q_strong : Q.strong.toList = j3Strong.map pkp :=
  certificate_strong_eq (by decide) _ j3Words #v[0, 2] (by decide) j3Strong rfl

theorem Q_valid : Q.check = true :=
  check_of_schV (by decide) _ j3Words #v[0, 2] (by decide) j3Strong Q_strong ch5253_j3_sch

theorem Q_card : Nat.card Q.originalSubgroup = 1920 := by
  rw [← Q.orderCertificate_eq_card Q_valid, orderCertificate_eq_ordV Q j3Strong Q_strong]
  unfold Q
  rw [ordV_certificate_base, Nat.eq_of_beq_eq_true ch5253_j3_ord]

theorem Q_mem (g : Equiv.Perm (Fin 80)) :
    g ∈ Q.originalSubgroup ↔ g ∈ (enumV j3Strong #v[0, 2]).map pkp := by
  rw [← mem_enumeration_iff Q Q_valid, enumeration_eq_enumV Q j3Strong Q_strong]
  rfl

theorem j3_noP
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ P W : Subgroup (Equiv.Perm (Fin 6156)), P ≤ j3P → W ≤ j3P → Nat.card P = 2 ^ 7 →
      IsPGroup p W → P ≤ normalizer (W : Set (Equiv.Perm (Fin 6156))) → W = ⊥ := by
  classical
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  set r0 := j3Rows[0]'(by simp [j3Rows]) with hr0def
  have hr0 : r0 ∈ j3Rows := List.getElem_mem _
  obtain ⟨-, ht2, -, hCr, hcard, -⟩ := hrows r0 hr0
  have hrep0 : r0.rep = j3CentTbl 9 := by simp [r0, j3Rows]
  have hcent0 : r0.centOrder = 1920 := by simp [r0, j3Rows]
  have hgens0 : r0.centGens =
      [j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14] := by
    simp [r0, j3Rows]
  rw [hrep0] at ht2 hCr hcard
  rw [hcent0] at hcard
  obtain ⟨T, hT⟩ : ∃ T, T = tp 6156 (j3CentTbl 9) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = j3C r0 := ⟨_, rfl⟩
  rw [← hT] at ht2 hCr hcard
  rw [← hKdef] at hCr
  have hKc : Nat.card K = 1920 := by rw [hCr]; exact hcard
  have hKP : K ≤ j3P := by rw [hCr]; exact inf_le_left
  have hGK : ∀ x ∈ r0.centGens, tp 6156 x ∈ K := by
    intro x hx
    rw [hKdef, j3C]
    exact subset_closure ⟨x, List.mem_toArray.2 hx, rfl⟩
  have hG : ∀ i, sG i ∈ K := by
    intro i
    rcases i with _ | _ | _ | _ | _ | i <;>
      simp only [sG, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
        List.getD_nil]
    all_goals first
      | exact one_mem _
      | exact hGK _ (by rw [hgens0]; simp)
  have hKS : K ≤ resStab o := by
    rw [hKdef, j3C, closure_le]
    rintro _ ⟨x, hx, hgx⟩
    rw [hgens0] at hx
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [← hgx]
    rcases hx with h | h | h | h | h <;> rw [h]
    · rw [← sG_eq0]
      exact (res_gen 0).1
    · rw [← sG_eq1]
      exact (res_gen 1).1
    · rw [← sG_eq2]
      exact (res_gen 2).1
    · rw [← sG_eq3]
      exact (res_gen 3).1
    · rw [← sG_eq4]
      exact (res_gen 4).1
  have hw := res_word hKS hG
  have hL : ∀ l ∈ Q.originalSubgroup, ∃ x, ∃ hx : x ∈ K, resHom o ⟨x, hKS hx⟩ = l := by
    have hle : Q.originalSubgroup ≤ (K.subgroupOf (resStab o)).map (resHom o) := by
      unfold Q
      rw [certificate_originalSubgroup, closure_le]
      rintro _ hz
      simp only [Set.mem_setOf_eq, List.map_map, List.mem_map, Function.comp_apply] at hz
      obtain ⟨w, -, rfl⟩ := hz
      refine ⟨⟨_, hKS (hw w).1⟩, (hw w).1, ?_⟩
      rw [resHom_eq_ρ, (hw w).2, pkp_evV]
    intro l hl
    obtain ⟨⟨x, hxS⟩, hxK, rfl⟩ := hle hl
    exact ⟨x, hxK, rfl⟩
  obtain ⟨hρK, hinj⟩ := res_injOn hKS hL (by rw [hKc, Q_card])
  have hinj' : ∀ x ∈ K, ∀ y ∈ K, ρ x = ρ y → x = y := fun x hx y hy h =>
    hinj x hx y hy (by rw [resHom_eq_ρ, resHom_eq_ρ]; exact h)
  have hLL : ∀ y (hy : y ∈ K), ∃ y' ∈ enumV j3Strong #v[0, 2], resHom o ⟨y, hKS hy⟩ = pkp y' := by
    intro y hy
    obtain ⟨y', hy', e⟩ := List.mem_map.1 ((Q_mem _).1 (hρK y hy))
    exact ⟨y', hy', e.symm⟩
  set Xs := j3Xw.map (wv sG sGi) with hXs
  set S : Set (Equiv.Perm (Fin 6156)) := {x | x ∈ Xs} with hS
  have hXK : ∀ x ∈ Xs, x ∈ K ∧ ρ x ∈ j3Xs.map pkp := by
    intro x hx
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hx
    refine ⟨(hw w).1, ?_⟩
    rw [(hw w).2, ← pkp_evV]
    exact List.mem_map_of_mem (List.mem_map_of_mem hw')
  have hxs := ch5253_j3_xs
  simp only [Bool.and_eq_true, List.all_eq_true] at hxs
  have hinvS : ∀ x ∈ S, x * x = 1 := by
    intro x hx
    obtain ⟨hxK, hρx⟩ := hXK x hx
    refine hinj' _ (mul_mem hxK hxK) _ (one_mem _) ?_
    rw [ρ_mul (hKS hxK) (hKS hxK), ρ_one]
    obtain ⟨u, hu, e⟩ := List.mem_map.1 hρx
    have := eq_of_not_difV (hxs.1 u hu : (!difV (mulV u u) (oneV 80)) = true)
    rw [pkp_mulV, pkp_oneV, e] at this
    exact this
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxK, hρx⟩ := hXK x hx
    obtain ⟨hyK, hρy⟩ := hXK y hy
    refine hinj' _ (mul_mem hxK hyK) _ (mul_mem hyK hxK) ?_
    rw [ρ_mul (hKS hxK) (hKS hyK), ρ_mul (hKS hyK) (hKS hxK)]
    obtain ⟨u, hu, e⟩ := List.mem_map.1 hρx
    obtain ⟨v, hv, e'⟩ := List.mem_map.1 hρy
    have := eq_of_not_difV (hxs.2 u hu v hv : (!difV (mulV u v) (mulV v u)) = true)
    rw [pkp_mulV, pkp_mulV, e, e'] at this
    exact this
  have hn : (6156 : ℕ) < 2 ^ 32 := by norm_num
  have hA : ∀ w, PRep 6156 (evA w) (wv sA sA w) := prep_evalN prep_gA prep_gA
  have hGw : ∀ w, PRep 6156 (evG w) (wv sG sGi w) :=
    prep_evalN (fun i => (prep_g1 i).1) (fun i => (prep_g1 i).2)
  have hT9 : PRep 6156 (J3CentP 9) T := by rw [hT]; exact (prep_cent (by norm_num)).1
  have hT10 : PRep 6156 (J3CentP 10) (sG 0) := by
    simp only [sG, List.map_cons, List.getD_cons_zero]
    exact (prep_cent (by norm_num)).1
  have hTeq : T = sG 0 := (prep_eq hT9 hT10).1 rep1_ok
  have hTT : T * T = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hT1 : T ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  set X₂ := wv sG sGi (j3Xw.getD 1 []) with hX₂
  have hX₃ : wv sG sGi (j3Xw.getD 2 []) = T := by
    have e : wv sG sGi (j3Xw.getD 2 []) = (sG 0)⁻¹ := by simp [j3Xw, wv, sGi]
    rw [e, ← hTeq]
    exact inv_eq_of_mul_eq_one_right hTT
  have hXS : ∀ j < 3, wv sG sGi (j3Xw.getD j []) ∈ S := by
    intro j hj
    refine List.mem_map_of_mem ?_
    rw [List.getD_eq_getElem _ _ (by simpa [j3Xw] using hj)]
    exact List.getElem_mem _
  have hXmem : ∀ j < 3, wv sG sGi (j3Xw.getD j []) ∈ closure S := fun j hj =>
    subset_closure (hXS j hj)
  have hTS : T ∈ closure S := by
    rw [← hX₃]
    exact hXmem 2 (by norm_num)
  have hX₂S : X₂ ∈ closure S := hXmem 1 (by norm_num)
  set C₁ := wv sA sA j3Cw with hC₁
  set Qg := wv sG sGi j3Qw with hQg
  have hconj := ch5253_j3_conj
  simp only [Bool.and_eq_true, List.all_eq_true] at hconj
  obtain ⟨⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩, hc5⟩ := hconj
  have hCi : wv sA sA j3Ciw = C₁⁻¹ :=
    eq_inv_of_mul_eq_one_left ((prep_eq (prep_pmN hn (hA _) (hA _)) (prep_pidn (by norm_num))).1 hc1)
  have hc2' : C₁ * T = X₂ * C₁ :=
    (prep_eq (prep_pmN hn (hA _) hT9) (prep_pmN hn (hGw _) (hA _))).1 hc2
  have hc3' : Qg * X₂ = T * X₂ * Qg :=
    (prep_eq (prep_pmN hn (hGw _) (hGw _))
      (prep_pmN hn (prep_pmN hn hT9 (hGw _)) (hGw _))).1 hc3
  have hQi : wv sG sGi j3Qiw = Qg⁻¹ :=
    eq_inv_of_mul_eq_one_left ((prep_eq (prep_pmN hn (hGw _) (hGw _)) (prep_pidn (by norm_num))).1 hc4)
  have hfr : ∀ {X : ℕ} {g : Equiv.Perm (Fin 6156)}, PRep 6156 X g →
      PRep 6156 (frN X) (C₁⁻¹ * g * C₁) := by
    intro X g hX
    have := prep_pmN hn (hA j3Ciw) (prep_pmN hn hX (hA j3Cw))
    rwa [hCi, ← mul_assoc] at this
  have hqN : ∀ {X : ℕ} {g : Equiv.Perm (Fin 6156)}, PRep 6156 X g →
      PRep 6156 (qN X) (Qg⁻¹ * g * Qg) := by
    intro X g hX
    have := prep_pmN hn (hGw j3Qiw) (prep_pmN hn hX (hGw j3Qw))
    rwa [hQi, ← mul_assoc] at this
  have hF0 : ∀ f ∈ j3Xs, ∃ x ∈ closure S, ∃ hx : (1 : Equiv.Perm (Fin 6156))⁻¹ * x * 1 ∈ resStab o,
      resHom o ⟨_, hx⟩ = pkp f := by
    intro f hf
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hf
    have e : (1 : Equiv.Perm (Fin 6156))⁻¹ * wv sG sGi w * 1 = wv sG sGi w := by group
    refine ⟨wv sG sGi w, subset_closure (List.mem_map_of_mem hw'), e ▸ hKS (hw w).1, ?_⟩
    rw [resHom_eq_ρ, e, (hw w).2, pkp_evV]
  have hF1 : ∀ f ∈ j3Fr1, ∃ x ∈ closure S, ∃ hx : C₁⁻¹ * x * C₁ ∈ resStab o,
      resHom o ⟨_, hx⟩ = pkp f := by
    intro f hf
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
    have hj3 : j < 3 := by rwa [j3Fr1_length] at hj
    have hr := (hc5 j (List.mem_range.2 hj3)).1
    rw [List.getD_eq_getElem _ _ hj] at hr
    obtain ⟨hm, hρ⟩ := res_of (hfr (hGw _)) hr
    exact ⟨_, hXmem j hj3, hm, by rw [resHom_eq_ρ, hρ]⟩
  have hF2 : ∀ f ∈ j3Fr2, ∃ x ∈ closure S, ∃ hx : (Qg * C₁)⁻¹ * x * (Qg * C₁) ∈ resStab o,
      resHom o ⟨_, hx⟩ = pkp f := by
    intro f hf
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
    have hj3 : j < 3 := by rwa [j3Fr2_length] at hj
    have hr := (hc5 j (List.mem_range.2 hj3)).2
    rw [List.getD_eq_getElem _ _ hj] at hr
    obtain ⟨hm, hρ⟩ := res_of (hfr (hqN (hGw _))) hr
    have e : C₁⁻¹ * (Qg⁻¹ * wv sG sGi (j3Xw.getD j []) * Qg) * C₁ =
        (Qg * C₁)⁻¹ * wv sG sGi (j3Xw.getD j []) * (Qg * C₁) := by group
    refine ⟨_, hXmem j hj3, e ▸ hm, ?_⟩
    rw [resHom_eq_ρ, ← e, hρ]
  have hw80 := ch5253_j3_w
  simp only [j3W, Bool.and_eq_true] at hw80
  obtain ⟨⟨⟨⟨⟨w1, w2⟩, w3⟩, w4⟩, w5⟩, w6⟩ := hw80
  have hwd : wd 80 = 7 := by decide
  have hN : ∀ y ∈ K, ∀ c ∈ [1, C₁, Qg * C₁], orderOf y = p →
      ∃ h ∈ closure S, h ∉ normalizer (zpowers (c * y * c⁻¹) : Set (Equiv.Perm (Fin 6156))) := by
    intro y hy c hc hyo
    have hp35 : p = 3 ∨ p = 5 := by
      refine prime_dvd_1920 hp hp2 ?_
      rw [← hKc, ← hyo, ← Subgroup.orderOf_mk y hy]
      exact orderOf_dvd_natCard _
    have key : ∀ (c : Equiv.Perm (Fin 6156)) (F : List (VP 80)),
        (∀ f ∈ F, ∃ x ∈ closure S, ∃ hx : c⁻¹ * x * c ∈ resStab o, resHom o ⟨_, hx⟩ = pkp f) →
        chkP 80 7 p (wits F) j3Enum = true →
        ∃ h ∈ closure S, h ∉ normalizer (zpowers (c * y * c⁻¹) : Set (Equiv.Perm (Fin 6156))) := by
      intro c F hF hck
      rw [← hwd] at hck
      exact hN_of_res (by norm_num) (by rw [hwd]; norm_num) hp hKS hinj c hF hLL hck y hy hyo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hp35 with rfl | rfl <;> rcases hc with rfl | rfl | rfl
    · exact key _ _ hF0 w1
    · exact key _ _ hF1 w3
    · exact key _ _ hF2 w5
    · exact key _ _ hF0 w2
    · exact key _ _ hF1 w4
    · exact key _ _ hF2 w6
  have hBB : X₂ * X₂ = 1 := hinvS X₂ (hXS 1 (by norm_num))
  have hAB : T * X₂ = X₂ * T := by
    rw [← hX₃]
    exact hcommS _ (hXS 2 (by norm_num)) _ (hXS 1 (by norm_num))
  have hX₂c : C₁ * T * C₁⁻¹ = X₂ := by rw [hc2', mul_inv_cancel_right]
  have hTX₂c : Qg * C₁ * T * (Qg * C₁)⁻¹ = T * X₂ := by
    calc Qg * C₁ * T * (Qg * C₁)⁻¹ = Qg * (C₁ * T * C₁⁻¹) * Qg⁻¹ := by group
      _ = Qg * X₂ * Qg⁻¹ := by rw [hX₂c]
      _ = T * X₂ := by rw [hc3', mul_inv_cancel_right]
  have hB1 : X₂ ≠ 1 := by
    intro h
    apply hT1
    have : C₁ * T * C₁⁻¹ = 1 := hX₂c.trans h
    calc T = C₁⁻¹ * (C₁ * T * C₁⁻¹) * C₁ := by group
      _ = 1 := by rw [this]; group
  have hAneB : T ≠ X₂ := by
    intro h
    apply hT1
    have h1 : Qg * C₁ * T * (Qg * C₁)⁻¹ = 1 := by rw [hTX₂c, ← h, hTT]
    calc T = (Qg * C₁)⁻¹ * (Qg * C₁ * T * (Qg * C₁)⁻¹) * (Qg * C₁) := by group
      _ = 1 := by rw [h1]; group
  have hcov : ∀ e ∈ [T, X₂, T * X₂], ∃ c ∈ [1, C₁, Qg * C₁], c * T * c⁻¹ = e := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨1, by simp, by group⟩
    · exact ⟨C₁, by simp, hX₂c⟩
    · exact ⟨Qg * C₁, by simp, hTX₂c⟩
  have hsA : ∀ i, sA i ∈ j3P := by
    intro i
    rcases i with _ | _ | i <;> simp only [sA, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil]
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact one_mem _
  have hcs : ∀ c ∈ [1, C₁, Qg * C₁], c ∈ j3P := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact one_mem _
    · exact wv_mem hsA hsA _
    · exact mul_mem (hKP (hw _).1) (wv_mem hsA hsA _)
  have hHS : closure S ≤ j3P := by
    rw [closure_le]
    intro x hx
    exact hKP (hXK x hx).1
  have hHc : ∀ h ∈ closure S, h * T = T * h ∧ h * X₂ = X₂ * h := fun h hh =>
    ⟨comm_of_mem_closure hcommS h hh _ hTS, comm_of_mem_closure hcommS h hh _ hX₂S⟩
  have hKmem : ∀ x ∈ j3P, x * T = T * x → x ∈ K := by
    intro x hx hxr
    rw [hCr, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨hx, hxr⟩
  have hpK : ¬ p ^ 2 ∣ Nat.card K := by
    rw [hKc]
    intro h
    rcases prime_dvd_1920 hp hp2 ((dvd_pow_self p two_ne_zero).trans h) with rfl | rfl <;>
      norm_num at h
  have hS₀ : ¬ 2 ^ (7 + 1) ∣ Nat.card j3P := by
    rw [card_j3P]
    norm_num
  exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.noP_of_cent le_rfl hp hp2 hTS hX₂S hTT hBB hAB hT1
    hB1 hAneB (isPGroup_two_closure hinvS hcommS) hHS hHc hKmem hpK hcs hcov hN hS₀

end CFSG.KS.Ivk8NormP.J3

end
