module

public import Certificates.Kernel.J2F3.Checks
public import Certificates.Kernel.Sporadic.OddCore.J2CnF
public import CFSG.Certificates.Kernel.SporSch.BasePtWitSound
public import CFSG.Certificates.Kernel.SporSch.MathieuOddGlue
public import CFSG.Sporadic.SmallOddCore.J2Local
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2F3

open Subgroup CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native Certificates.Odd87F3 Certificates.Odd87F3.J2
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.MulH CFSG.KS.SporSch.BPW
open CertificateChecks.KernelSpor CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem hn : (315 : ℕ) < 2 ^ 32 := by norm_num

theorem hsz : szOK 315 9 = true := J2Cn.hn

theorem prep_of_tab {P : Nat} {T : Table} {g : Equiv.Perm (Fin 315)}
    (hc : canonK 315 9 (mask 9) (315 * 9) P = true) (hT : T = tabT (unpack 315 9 P))
    (h : Rep 315 T g) : PRep 315 9 P g := by
  subst hT
  intro x
  have e := h x.val x.2
  rw [ap_tabT _ (unpack_lt hc), unpack_get x.2, idx_of_lt _ x.2] at e
  exact e

noncomputable abbrev cT (k : Nat) : Equiv.Perm (Fin 315) := tp 315 (j2CentTbl k)

theorem repC {k : Nat} (hk : k < 42) : Rep 315 (j2CentTbl k) (cT k) := rep_tp (J2Cn.permF hk)

theorem pC {k : Nat} (hk : k < 42) : PRep 315 9 (J2CentT.F k) (cT k) :=
  prep_of_tab (J2Cn.Fc hk) (J2Cn.tabF hk) (repC hk)

theorem pCI {k : Nat} (hk : k < 42) : PRep 315 9 (J2CentI k) (cT k)⁻¹ :=
  prep_of_tab (J2Cn.Ic hk) (J2Cn.invF hk) (CFSG.KS.Tbl.invT_rep hn (repC hk))

theorem pS {j : Nat} (hj : j < 2) :
    PRep 315 9 (J2P.S j) (j2Gen j) :=
  prep_of_tab (J2Cn.pg_tabs.2 j hj).2 (J2Cn.pg_tabs.2 j hj).1
    (j2_groupData.rep j (by rw [J2Cn.pg_tabs.1]; exact hj))

theorem pSI {j : Nat} (hj : j < 2) :
    PRep 315 9 (J2P.SI j) (j2Gen j)⁻¹ := by
  have hl : j < j2PGTbls.size := by rw [J2Cn.pg_tabs.1]; exact hj
  have e : j2PGInvTbls[j]! = invT 315 j2PGTbls[j]! := by
    rw [getElem!_pos _ j (by simpa [j2PGInvTbls] using hl), getElem!_pos _ j hl]
    simp [j2PGInvTbls]
  refine prep_of_tab (J2Cn.pgi_tabs.2 j hj).2 (J2Cn.pgi_tabs.2 j hj).1 ?_
  rw [e]
  exact CFSG.KS.Tbl.invT_rep hn (j2_groupData.rep j hl)

theorem j2P_eq : j2P = closure (Set.range fun j : Fin 2 => j2Gen j) := by
  rw [j2P]
  congr 1
  ext g
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨⟨_ | _ | j, hj⟩, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega

theorem gR {G GI : Nat → Nat}
    (h : allN 2 (fun j => bAnd(Nat.beq (G j) (J2P.S j), Nat.beq (GI j) (J2P.SI j))) = true) :
    ∀ j < 2, PRep 315 9 (G j) (j2Gen j) ∧ PRep 315 9 (GI j) (j2Gen j)⁻¹ := fun j hj => by
  rw [(J2Cn.pair_of h).1 j hj, (J2Cn.pair_of h).2 j hj]
  exact ⟨pS hj, pSI hj⟩

theorem cls1 :
    ∀ g ∈ j2P, ∃ i < J2R1.cnt, PRep 315 9 (J2R1.T i) (g * cT 9 * g⁻¹) := by
  intro g hg
  rw [j2P_eq] at hg
  refine penum_conj_closed hsz (gR J2Cn.bindO.1.1) J2Cn.heads.1 J2Cn.r1_pe ?_ g hg
  rw [Nat.eq_of_beq_eq_true J2Cn.bindO.2.1]
  exact pC (by norm_num)

theorem cls2 :
    ∀ g ∈ j2P, ∃ i < J2R2.cnt, PRep 315 9 (J2R2.T i) (g * cT 17 * g⁻¹) := by
  intro g hg
  rw [j2P_eq] at hg
  refine penum_conj_closed hsz (gR J2Cn.bindO.1.2.1) J2Cn.heads.2.1 J2Cn.r2_pe ?_ g hg
  rw [Nat.eq_of_beq_eq_true J2Cn.bindO.2.2.1]
  exact pC (by norm_num)

theorem cls3 :
    ∀ g ∈ j2P, ∃ i < J2R3.cnt, PRep 315 9 (J2R3.T i) (g * cT 31 * g⁻¹) := by
  intro g hg
  rw [j2P_eq] at hg
  refine penum_conj_closed hsz (gR J2Cn.bindO.1.2.2) J2Cn.heads.2.2.1 (J2Cn.pe_all' J2Cn.o3E) ?_
    g hg
  rw [Nat.eq_of_beq_eq_true J2Cn.bindO.2.2.2]
  exact pC (by norm_num)

theorem rows_eq : j2Rows = [rowAt 0, rowAt 1, rowAt 2] := rfl

theorem rowF
    (i : Fin 3) :
    tp 315 (rowAt i).rep ∈ j2R ∧ orderOf (tp 315 (rowAt i).rep) = 2 ∧
      ((rowAt i).outer = true ↔ tp 315 (rowAt i).rep ∉ j2P) ∧
      j2C (rowAt i) = j2P ⊓ centralizer ({tp 315 (rowAt i).rep} : Set _) := by
  obtain ⟨-, -, -, hrows, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨h1, h2, h3, h4, -⟩ := hrows (rowAt i) (List.getElem_mem _)
  exact ⟨h1, h2, h3, h4⟩

theorem comm_of
    (i : Fin 3) {T : Table} (hT : T ∈ (rowAt i).centGens) :
    tp 315 (rowAt i).rep * tp 315 T = tp 315 T * tp 315 (rowAt i).rep := by
  have hmem : tp 315 T ∈ j2C (rowAt i) := Subgroup.subset_closure ⟨T, by simpa using hT, rfl⟩
  rw [(rowF i).2.2.2] at hmem
  have h := Subgroup.mem_centralizer_singleton_iff.1 hmem.2
  first
  | exact h
  | exact h.symm

theorem sq_of {t : Equiv.Perm (Fin 315)} (h : orderOf t = 2) : t * t = 1 := by
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem conj_mem_iff {g t : Equiv.Perm (Fin 315)} (hg : g ∈ j2P) :
    g * t * g⁻¹ ∈ j2P ↔ t ∈ j2P := by
  constructor
  · intro h
    have e : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [e]
    exact j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) h) hg
  · intro h
    exact j2P.mul_mem (j2P.mul_mem hg h) (j2P.inv_mem hg)

theorem s_cases
    {u s : Equiv.Perm (Fin 315)} (hu : u ∈ j2R)
    (hss : s * s = 1) (hus : u * s ∈ j2P) :
    s = 1 ∨ ∃ i : Fin 3, ∃ g ∈ j2P, s = g * tp 315 (rowAt i).rep * g⁻¹ ∧
      (tp 315 (rowAt i).rep ∈ j2P ↔ u ∈ j2P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hcover, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  by_cases h1 : s = 1
  · exact Or.inl h1
  right
  have hsR : s ∈ j2R := by
    have e : s = u⁻¹ * (u * s) := by group
    rw [e]
    exact j2R.mul_mem (j2R.inv_mem hu) (j2P_le_j2R hus)
  obtain ⟨r, hr, g, hg, hrs⟩ := hcover s hsR (orderOf_eq_prime (by rw [pow_two]; exact hss) h1)
  have hsu : s ∈ j2P ↔ u ∈ j2P := by
    constructor
    · intro h
      have e : u = (u * s) * s⁻¹ := by group
      rw [e]
      exact j2P.mul_mem hus (j2P.inv_mem h)
    · intro h
      have e : s = u⁻¹ * (u * s) := by group
      rw [e]
      exact j2P.mul_mem (j2P.inv_mem h) hus
  rw [rows_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have key : ∀ i : Fin 3, r = rowAt i → ∃ i : Fin 3, ∃ g ∈ j2P, s = g * tp 315 (rowAt i).rep * g⁻¹ ∧
      (tp 315 (rowAt i).rep ∈ j2P ↔ u ∈ j2P) := by
    rintro i rfl
    refine ⟨i, g, hg, hrs, ?_⟩
    rw [← hsu, hrs, conj_mem_iff hg]
  rcases hr with h | h | h
  · exact key 0 h
  · exact key 1 h
  · exact key 2 h

theorem forall₂_zip {R : Nat × Nat → Equiv.Perm (Fin 315) → Prop}
    {f : List ℤ → Equiv.Perm (Fin 315)} : ∀ {ws : List (List ℤ)} {P PI : List Nat},
    P.length = ws.length → PI.length = ws.length →
    (∀ i < ws.length, R (P.getD i 0, PI.getD i 0) (f (ws.getD i []))) →
    List.Forall₂ R (P.zip PI) (ws.map f)
  | [], P, PI, h1, _, _ => by
    rw [List.length_nil, List.length_eq_zero_iff] at h1
    subst h1
    exact .nil
  | _ :: _, [], _, h1, _, _ => absurd h1 (by simp)
  | _ :: _, _ :: _, [], _, h2, _ => absurd h2 (by simp)
  | wd :: ws, a :: P, b :: PI, h1, h2, h =>
    .cons (h 0 (by simp)) (forall₂_zip (by simpa using h1) (by simpa using h2)
      fun i hi => h (i + 1) (by simp; omega))

theorem wordsOK_sound {gP gI : List Nat} {gs : List (Equiv.Perm (Fin 315))}
    (h1 : List.Forall₂ (PRep 315 9) gP gs) (h2 : List.Forall₂ (PRep 315 9) gI (gs.map fun g => g⁻¹))
    {ws : List (List ℤ)} {m : Nat}
    (hws : ∀ wd ∈ ws, ∀ z ∈ wd, (if 0 < z then z.toNat - 1 else (-z).toNat - 1) < m)
    (hm : m ≤ gs.length) {P PI : List Nat} {e : Nat} (h : wordsOK gP gI ws P PI e = true) :
    List.Forall₂ (fun Q c => PRep 315 9 Q.1 c ∧ PRep 315 9 Q.2 c⁻¹) (P.zip PI)
      (ws.map (evalCodes gs)) ∧ ∀ c ∈ ws.map (evalCodes gs), c ^ e = 1 := by
  unfold wordsOK at h
  obtain ⟨hl1, h'⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hl2, hall⟩ := (bAnd_iff _ _).1 h'
  have hat : ∀ i < ws.length, PRep 315 9 (P.getD i 0) (evalCodes gs (ws.getD i [])) ∧
      PRep 315 9 (PI.getD i 0) (evalCodes gs (ws.getD i []))⁻¹ ∧
      evalCodes gs (ws.getD i []) ^ e = 1 := by
    intro i hi
    obtain ⟨b1, h3⟩ := (bAnd_iff _ _).1 (allN_spec hall i hi)
    obtain ⟨-, h4⟩ := (bAnd_iff _ _).1 h3
    obtain ⟨b3, b4⟩ := (bAnd_iff _ _).1 h4
    have hwd : ws.getD i [] ∈ ws := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem _
    have pP : PRep 315 9 (P.getD i 0) (evalCodes gs (ws.getD i [])) := by
      rw [Nat.eq_of_beq_eq_true b1]
      exact prep_wordK hsz h1 h2 fun z hz => Nat.lt_of_lt_of_le (hws _ hwd z hz) hm
    refine ⟨pP, ?_, CFSG.KS.SporSch.OddWit.pow_eq_one_of hsz pP b4⟩
    rw [Nat.eq_of_beq_eq_true b3]
    exact (CFSG.KS.SporSch.MOC.prep_pinvS (by norm_num) pP).1
  refine ⟨forall₂_zip (Nat.eq_of_beq_eq_true hl1) (Nat.eq_of_beq_eq_true hl2)
    fun i hi => ⟨(hat i hi).1, (hat i hi).2.1⟩, fun c hc => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hi' : i < ws.length := by simpa using hi
  have := (hat i hi').2.2
  rw [List.getD_eq_getElem _ _ hi'] at this
  simpa using this

theorem valid :
    ValidSchreier j2Chain := j2Chain_valid.1

theorem hbs : ∀ i : Fin j2Chain.baseCount, (j2Chain.base.get i).val ∈ bs := by
  intro i
  have h : (j2Chain.base.get i).val ∈ j2Chain.base.toList.map Fin.val := by
    refine List.mem_map_of_mem ?_
    first
    | exact List.Vector.get_mem i j2Chain.base
    | simp [Vector.get]
  rw [j2Chain_base] at h
  exact h

theorem hlt : ∀ b ∈ bs, b < 315 := by decide

theorem hTss :
    levelTables j2Chain = j2Tss :=
  CFSG.ComponentClassification.J2Cover.levelTables_eq j2ChainArrays
    (chainCheckFacts PairJ2.chain_check.1)

theorem cand_of {U : Nat}
    {u : Equiv.Perm (Fin 315)} (pU : PRep 315 9 U u) (hu2 : u * u = 1)
    {rows : List (Nat × Nat × List (Nat × Nat))}
    (hS : ∀ s : Equiv.Perm (Fin 315), s * s = 1 → u * s ∈ j2P →
      ∃ S, PRep 315 9 S s ∧ rowsB 9 U S bs rows = true)
    {p e : Nat} {OG : List (Nat × Nat)} (hr : (p, e, OG) ∈ rows) {cs : List (Equiv.Perm (Fin 315))}
    (hOG : List.Forall₂ (fun P c => PRep 315 9 P.1 c ∧ PRep 315 9 P.2 c⁻¹) OG cs) (hp : p ≠ 1) :
    ∀ x ∈ j2Chain.originalSubgroup, (u * x) * (u * x) = 1 → orderOf x = p →
      (∃ c ∈ cs, (x * c * x * c⁻¹) ^ e ≠ 1) ∨
        ∃ c₁ ∈ cs, ∃ c₂ ∈ cs, (x * c₁ * x * c₁⁻¹ * c₂ * x * c₂⁻¹) ^ e ≠ 1 := by
  intro x hx hsq ho
  have e1 : u * (u * x) = x := by rw [← mul_assoc, hu2, one_mul]
  have hxP : u * (u * x) ∈ j2P := by
    rw [e1, j2P_eq_original]
    exact hx
  obtain ⟨S, pS', hS'⟩ := hS (u * x) hsq hxP
  have := rowsB_sound valid hbs hlt pU pS' (by rw [e1]; exact hx) hS' hr hOG hp
    (by rw [e1]; exact ho)
  rw [e1] at this
  exact this

theorem blk {T : Nat → Nat} {cnt len : Nat} {U : Nat}
    {rows : List (Nat × Nat × List (Nat × Nat))} (h : candB 9 U bs rows T cnt 0 len = true)
    (hc : cnt = len) {i : Nat} (hi : i < cnt) : rowsB 9 U (T i) bs rows = true :=
  candB_spec h i (Nat.zero_le _) (by omega) hi

theorem pId : PRep 315 9 (pidn 315 9) 1 := prep_pidn (by norm_num) (by norm_num)

theorem o1 : (rowAt 1).outer = false := rfl

theorem o2 : (rowAt 2).outer = false := rfl

theorem out0 :
    cT 9 ∉ j2P := (rowF 0).2.2.1.1 rfl

theorem in1 :
    cT 17 ∈ j2P :=
  not_not.1 ((rowF 1).2.2.1.not.1 (by rw [o1]; exact Bool.false_ne_true))

theorem in2 :
    cT 31 ∈ j2P :=
  not_not.1 ((rowF 2).2.2.1.not.1 (by rw [o2]; exact Bool.false_ne_true))

theorem hS1 :
    ∀ s : Equiv.Perm (Fin 315), s * s = 1 → cT 9 * s ∈ j2P →
    ∃ S, PRep 315 9 S s ∧ rowsB 9 (J2CentT.F 9) S bs rows1 = true := by
  intro s hss hus
  rcases s_cases (rowF 0).1 hss hus with rfl | ⟨i, g, hg, rfl, hi⟩
  · rw [mul_one] at hus
    exact absurd hus out0
  · fin_cases i
    · obtain ⟨k, hk, pk⟩ := cls1 g hg
      exact ⟨_, pk, blk ch5165r1 J2Cn.sizes.1 hk⟩
    · exact absurd (hi.1 in1) out0
    · exact absurd (hi.1 in2) out0

theorem hS2 :
    ∀ s : Equiv.Perm (Fin 315), s * s = 1 → cT 17 * s ∈ j2P →
    ∃ S, PRep 315 9 S s ∧ rowsB 9 (J2CentT.F 17) S bs rows2 = true := by
  intro s hss hus
  rcases s_cases (rowF 1).1 hss hus with rfl | ⟨i, g, hg, rfl, hi⟩
  · exact ⟨_, pId, ch5165r2c⟩
  · fin_cases i
    · exact absurd (hi.2 in1) out0
    · obtain ⟨k, hk, pk⟩ := cls2 g hg
      exact ⟨_, pk, blk ch5165r2a J2Cn.sizes.2.1 hk⟩
    · obtain ⟨k, hk, pk⟩ := cls3 g hg
      exact ⟨_, pk, blk ch5165r2b J2Cn.sizes.2.2.1 hk⟩

theorem hS3 :
    ∀ s : Equiv.Perm (Fin 315), s * s = 1 → cT 31 * s ∈ j2P →
    ∃ S, PRep 315 9 S s ∧ rowsB 9 (J2CentT.F 31) S bs rows3 = true := by
  intro s hss hus
  rcases s_cases (rowF 2).1 hss hus with rfl | ⟨i, g, hg, rfl, hi⟩
  · exact ⟨_, pId, ch5165r3c⟩
  · fin_cases i
    · exact absurd (hi.2 in2) out0
    · obtain ⟨k, hk, pk⟩ := cls2 g hg
      exact ⟨_, pk, blk ch5165r3a J2Cn.sizes.2.1 hk⟩
    · obtain ⟨k, hk, pk⟩ := cls3 g hg
      exact ⟨_, pk, blk ch5165r3b J2Cn.sizes.2.2.1 hk⟩

noncomputable abbrev gs1 : List (Equiv.Perm (Fin 315)) := [cT 10, cT 11, cT 12]

noncomputable abbrev gs2 : List (Equiv.Perm (Fin 315)) := [cT 18, cT 19, cT 20, cT 21, cT 22]

noncomputable abbrev gs3 : List (Equiv.Perm (Fin 315)) := [cT 32, cT 33, cT 34, cT 35]

theorem pg1 : List.Forall₂ (PRep 315 9) gP1 gs1 :=
  .cons (pC (by norm_num)) (.cons (pC (by norm_num)) (.cons (pC (by norm_num)) .nil))

theorem pgI1 : List.Forall₂ (PRep 315 9) gI1 (gs1.map fun g => g⁻¹) :=
  .cons (pCI (by norm_num)) (.cons (pCI (by norm_num)) (.cons (pCI (by norm_num)) .nil))

theorem pg2 : List.Forall₂ (PRep 315 9) gP2 gs2 :=
  .cons (pC (by norm_num)) (.cons (pC (by norm_num)) (.cons (pC (by norm_num))
    (.cons (pC (by norm_num)) (.cons (pC (by norm_num)) .nil))))

theorem pgI2 : List.Forall₂ (PRep 315 9) gI2 (gs2.map fun g => g⁻¹) :=
  .cons (pCI (by norm_num)) (.cons (pCI (by norm_num)) (.cons (pCI (by norm_num))
    (.cons (pCI (by norm_num)) (.cons (pCI (by norm_num)) .nil))))

theorem pg3 : List.Forall₂ (PRep 315 9) gP3 gs3 :=
  .cons (pC (by norm_num)) (.cons (pC (by norm_num)) (.cons (pC (by norm_num))
    (.cons (pC (by norm_num)) .nil)))

theorem pgI3 : List.Forall₂ (PRep 315 9) gI3 (gs3.map fun g => g⁻¹) :=
  .cons (pCI (by norm_num)) (.cons (pCI (by norm_num)) (.cons (pCI (by norm_num))
    (.cons (pCI (by norm_num)) .nil)))

theorem rg1 : List.Forall₂ (Rep 315) (rowAt 0).centGens gs1 :=
  .cons (repC (by norm_num)) (.cons (repC (by norm_num)) (.cons (repC (by norm_num)) .nil))

theorem rg2 : List.Forall₂ (Rep 315) (rowAt 1).centGens gs2 :=
  .cons (repC (by norm_num)) (.cons (repC (by norm_num)) (.cons (repC (by norm_num))
    (.cons (repC (by norm_num)) (.cons (repC (by norm_num)) .nil))))

theorem rg3 : List.Forall₂ (Rep 315) (rowAt 2).centGens gs3 :=
  .cons (repC (by norm_num)) (.cons (repC (by norm_num)) (.cons (repC (by norm_num))
    (.cons (repC (by norm_num)) .nil)))

theorem hpm0 : ∀ T ∈ (rowAt 0).centGens, permOK 315 T = true := by
  intro T hT
  change T ∈ [j2CentTbl 10, j2CentTbl 11, j2CentTbl 12] at hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl <;> exact J2Cn.permF (by norm_num)

theorem hpm1 : ∀ T ∈ (rowAt 1).centGens, permOK 315 T = true := by
  intro T hT
  change T ∈ [j2CentTbl 18, j2CentTbl 19, j2CentTbl 20, j2CentTbl 21, j2CentTbl 22] at hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl <;> exact J2Cn.permF (by norm_num)

theorem hpm2 : ∀ T ∈ (rowAt 2).centGens, permOK 315 T = true := by
  intro T hT
  change T ∈ [j2CentTbl 32, j2CentTbl 33, j2CentTbl 34, j2CentTbl 35] at hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl <;> exact J2Cn.permF (by norm_num)

theorem comm_gs
    (i : Fin 3) (hp : ∀ T ∈ (rowAt i).centGens, permOK 315 T = true)
    {gs : List (Equiv.Perm (Fin 315))} (hg : List.Forall₂ (Rep 315) (rowAt i).centGens gs) :
    ∀ g ∈ gs, tp 315 (rowAt i).rep * g = g * tp 315 (rowAt i).rep := by
  intro g hgm
  obtain ⟨T, hT, rT⟩ := exists_of_mem_right_forall₂ hg hgm
  have e : g = tp 315 T := rep_unique rT (rep_tp (hp T hT))
  rw [e]
  exact comm_of i hT

theorem rows1OK :
    rowsOKT 315 604800 j2Tss (rowAt 0).centGens (rowAt 0).rep rowsR1 = true := by
  have hu2 : cT 9 * cT 9 = 1 := sq_of (rowF 0).2.1
  have w3 := wordsOK_sound pg1 pgI1 (m := 3) (by decide) le_rfl ch5165w13
  have w7 := wordsOK_sound pg1 pgI1 (m := 3) (by decide) le_rfl ch5165w17
  unfold rowsOKT
  simp only [rowsR1, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨rowOKT_of hn j2Chain valid hTss rg1 (repC (k := 9) (by norm_num)) hu2 (comm_gs 0 hpm0 rg1)
      ⟨3, 3, 3, _⟩ (by norm_num) (by norm_num) (by norm_num) w3.2
      (cand_of (pC (k := 9) (by norm_num)) hu2 hS1 (by decide) w3.1 (by norm_num)),
    rowOKT_of hn j2Chain valid hTss rg1 (repC (k := 9) (by norm_num)) hu2 (comm_gs 0 hpm0 rg1)
      ⟨5, 2, 1, []⟩ (by norm_num) (by norm_num) (by norm_num) (by simp)
      (cand_of (pC (k := 9) (by norm_num)) hu2 hS1 (by decide) .nil (by norm_num)),
    rowOKT_of hn j2Chain valid hTss rg1 (repC (k := 9) (by norm_num)) hu2 (comm_gs 0 hpm0 rg1)
      ⟨7, 1, 3, _⟩ (by norm_num) (by norm_num) (by norm_num) w7.2
      (cand_of (pC (k := 9) (by norm_num)) hu2 hS1 (by decide) w7.1 (by norm_num))⟩

theorem rows2OK :
    rowsOKT 315 604800 j2Tss (rowAt 1).centGens (rowAt 1).rep rowsR2 = true := by
  have hu2 : cT 17 * cT 17 = 1 := sq_of (rowF 1).2.1
  have w3 := wordsOK_sound pg2 pgI2 (m := 5) (by decide) le_rfl ch5165w23
  have w5 := wordsOK_sound pg2 pgI2 (m := 5) (by decide) le_rfl ch5165w25
  have w7 := wordsOK_sound pg2 pgI2 (m := 5) (by decide) le_rfl ch5165w27
  unfold rowsOKT
  simp only [rowsR2, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨rowOKT_of hn j2Chain valid hTss rg2 (repC (k := 17) (by norm_num)) hu2 (comm_gs 1 hpm1 rg2)
      ⟨3, 3, 3, _⟩ (by norm_num) (by norm_num) (by norm_num) w3.2
      (cand_of (pC (k := 17) (by norm_num)) hu2 hS2 (by decide) w3.1 (by norm_num)),
    rowOKT_of hn j2Chain valid hTss rg2 (repC (k := 17) (by norm_num)) hu2 (comm_gs 1 hpm1 rg2)
      ⟨5, 2, 3, _⟩ (by norm_num) (by norm_num) (by norm_num) w5.2
      (cand_of (pC (k := 17) (by norm_num)) hu2 hS2 (by decide) w5.1 (by norm_num)),
    rowOKT_of hn j2Chain valid hTss rg2 (repC (k := 17) (by norm_num)) hu2 (comm_gs 1 hpm1 rg2)
      ⟨7, 1, 5, _⟩ (by norm_num) (by norm_num) (by norm_num) w7.2
      (cand_of (pC (k := 17) (by norm_num)) hu2 hS2 (by decide) w7.1 (by norm_num))⟩

theorem rows3OK :
    rowsOKT 315 604800 j2Tss (rowAt 2).centGens (rowAt 2).rep rowsR3 = true := by
  have hu2 : cT 31 * cT 31 = 1 := sq_of (rowF 2).2.1
  have w3 := wordsOK_sound pg3 pgI3 (m := 4) (by decide) le_rfl ch5165w33
  have w5 := wordsOK_sound pg3 pgI3 (m := 4) (by decide) le_rfl ch5165w35
  unfold rowsOKT
  simp only [rowsR3, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨rowOKT_of hn j2Chain valid hTss rg3 (repC (k := 31) (by norm_num)) hu2 (comm_gs 2 hpm2 rg3)
      ⟨3, 3, 3, _⟩ (by norm_num) (by norm_num) (by norm_num) w3.2
      (cand_of (pC (k := 31) (by norm_num)) hu2 hS3 (by decide) w3.1 (by norm_num)),
    rowOKT_of hn j2Chain valid hTss rg3 (repC (k := 31) (by norm_num)) hu2 (comm_gs 2 hpm2 rg3)
      ⟨5, 2, 5, _⟩ (by norm_num) (by norm_num) (by norm_num) w5.2
      (cand_of (pC (k := 31) (by norm_num)) hu2 hS3 (by decide) w5.1 (by norm_num)),
    rowOKT_of hn j2Chain valid hTss rg3 (repC (k := 31) (by norm_num)) hu2 (comm_gs 2 hpm2 rg3)
      ⟨7, 1, 1, []⟩ (by norm_num) (by norm_num) (by norm_num) (by simp)
      (cand_of (pC (k := 31) (by norm_num)) hu2 hS3 (by decide) .nil (by norm_num))⟩

theorem permsOK : ((List.finRange 3).all fun i =>
    permOK 315 (rowAt i).rep && (rowAt i).centGens.all (permOK 315)) = true := by
  rw [List.all_eq_true]
  intro i _
  rw [Bool.and_eq_true, List.all_eq_true]
  match i with
  | ⟨0, _⟩ => exact ⟨J2Cn.permF (k := 9) (by norm_num), hpm0⟩
  | ⟨1, _⟩ => exact ⟨J2Cn.permF (k := 17) (by norm_num), hpm1⟩
  | ⟨2, _⟩ => exact ⟨J2Cn.permF (k := 31) (by norm_num), hpm2⟩
  | ⟨j + 3, h⟩ => exact absurd h (by omega)

theorem f3OK :
    j2F3OK = true := by
  unfold j2F3OK
  simp only [permsOK, rows1OK, rows2OK, rows3OK, Bool.and_self]

end CertificateChecks.KernelJ2F3

end
