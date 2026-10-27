module

public import Certificates.Kernel.McLCls.Glue4
public import CFSG.Quasithin.Vol2.KGFactC31RuHyp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLCls

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.M305
  CertificateChecks.KernelLC.McLC CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Quasithin.KGC31
  CFSG.SectionRank.QTK.Insp443.McLCls CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore.Native CFSG.KS.MulH


theorem nrm_go {m : Nat} : ∀ {L cs : List Nat},
    (List.rec (motive := fun _ => List Nat → Bool)
      (fun cs => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) cs)
      (fun b _ ih cs => List.rec (motive := fun _ => Bool) false
        (fun c cs' _ => bAnd(Nat.beq (m305mul m b) (m305mul (m305prod bs c) m), ih cs')) cs) L)
      cs = true →
    List.Forall₂ (fun b c => Nat.beq (m305mul m b) (m305mul (m305prod bs c) m) = true) L cs
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | b :: L, c :: cs, h => by
    change bAnd(Nat.beq (m305mul m b) (m305mul (m305prod bs c) m), _) = true at h
    rw [band] at h
    exact List.Forall₂.cons h.1 (nrm_go h.2)

theorem norm_of {P : Nat} {m : Equiv.Perm (Fin 275)} (hm : PRep 275 9 P m)
    (h : ∀ i : Fin 4, ∃ c, Nat.beq (m305mul P (bsF i)) (m305mul (m305prod bs c) P) = true) :
    m ∈ eNorm basis_fact := by
  rw [mem_eNorm_iff basis_fact]
  intro i
  obtain ⟨c, hc⟩ := h i
  have e := eq_of_beq (prep_mul hm (prep_bsF i)) (prep_mul (prep_prod4 c) hm) hc
  have hv : F.v i = vs[i] := congrFun v_eq i
  refine ⟨bitVec 4 c, ?_⟩
  rw [hv, e, mul_inv_cancel_right]

theorem nrm_parts : (∀ i : Fin 4, ∃ c, Nat.beq (m305mul (CT.F 4) (bsF i))
      (m305mul (m305prod bs c) (CT.F 4)) = true) ∧
    (∀ i : Fin 4, ∃ c, Nat.beq (m305mul (CT.F 5) (bsF i))
      (m305mul (m305prod bs c) (CT.F 5)) = true) ∧
    Nat.beq (m305mul (CT.F 4) (MC.F 4)) (m305mul (MC.F 4) (CT.F 4)) = false := by
  have h := nrm
  rw [band, band] at h
  obtain ⟨h1, h2, h3⟩ := h
  have f1 := nrm_go (m := CT.F 4) (L := bs) (cs := nthW nrmC 0) h1
  have f2 := nrm_go (m := CT.F 5) (L := bs) (cs := nthW nrmC 1) h2
  unfold nthW nrmC at f1 f2
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · obtain ⟨a0, f1⟩ := List.forall₂_cons.mp f1
    obtain ⟨a1, f1⟩ := List.forall₂_cons.mp f1
    obtain ⟨a2, f1⟩ := List.forall₂_cons.mp f1
    obtain ⟨a3, -⟩ := List.forall₂_cons.mp f1
    fin_cases i
    · exact ⟨_, a0⟩
    · exact ⟨_, a1⟩
    · exact ⟨_, a2⟩
    · exact ⟨_, a3⟩
  · obtain ⟨a0, f2⟩ := List.forall₂_cons.mp f2
    obtain ⟨a1, f2⟩ := List.forall₂_cons.mp f2
    obtain ⟨a2, f2⟩ := List.forall₂_cons.mp f2
    obtain ⟨a3, -⟩ := List.forall₂_cons.mp f2
    fin_cases i
    · exact ⟨_, a0⟩
    · exact ⟨_, a1⟩
    · exact ⟨_, a2⟩
    · exact ⟨_, a3⟩
  · cases e : Nat.beq (m305mul (CT.F 4) (MC.F 4)) (m305mul (MC.F 4) (CT.F 4))
    · rfl
    · rw [e] at h3
      exact absurd h3 Bool.false_ne_true

@[expose] noncomputable def gM (j : Nat) : Equiv.Perm (Fin 275) :=
  Nat.rec (motive := fun _ => Equiv.Perm (Fin 275)) (tp 275 (clsTbl 4))
    (fun _ _ => tp 275 (clsTbl 5)) j

theorem prep_mL (j : Nat) : PRep 275 9 (mL j) (gM j) := by
  cases j
  · exact prep_cls (k := 4) (by norm_num)
  · exact prep_cls (k := 5) (by norm_num)

theorem gM_mem (j : Nat) : gM j ∈ F.M := by
  apply Subgroup.subset_closure
  cases j
  · exact ⟨clsTbl 4, by simp [mGens], rfl⟩
  · exact ⟨clsTbl 5, by simp [mGens], rfl⟩

theorem M_le_eNorm : F.M ≤ eNorm basis_fact := by
  change closure (tp 275 '' {x | x ∈ mGens.toArray}) ≤ _
  rw [closure_le]
  rintro _ ⟨T, hT, rfl⟩
  simp only [mGens, List.toArray, Set.mem_setOf_eq, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl
  · exact norm_of (prep_cls (k := 4) (by norm_num)) nrm_parts.1
  · exact norm_of (prep_cls (k := 5) (by norm_num)) nrm_parts.2.1

theorem W_le_M : F.W ≤ F.M := by
  have h := words_forall₂ mWords
  unfold mWd at h
  obtain ⟨h0, h⟩ := List.forall₂_cons.mp h
  obtain ⟨h1, h⟩ := List.forall₂_cons.mp h
  obtain ⟨h2, h⟩ := List.forall₂_cons.mp h
  obtain ⟨h3, -⟩ := List.forall₂_cons.mp h
  have wm : ∀ wd : List Nat, (wd.map gM).prod ∈ F.M := fun wd =>
    F.M.list_prod_mem fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      exact gM_mem j
  have key : ∀ (i : Fin 4) (wd : List Nat), Nat.beq (m305word mL wd) (bsF i) = true →
      F.v i ∈ F.M := by
    intro i wd e
    rw [congrFun v_eq i, ← eq_of_beq (prep_word prep_mL wd) (prep_bsF i) e]
    exact wm wd
  rw [closure_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact key 0 _ h0
  · exact key 1 _ h1
  · exact key 2 _ h2
  · exact key 3 _ h3

theorem M_le_norm : F.M ≤ normalizer (F.W : Set (Equiv.Perm (Fin 275))) := by
  rw [W_eq]
  exact M_le_eNorm

theorem M_le_setStab : F.M ≤ setStab F.O := fun g hg =>
  mem_setStab_of_normalizer basis_fact (fun i => fixO i) (M_le_eNorm hg)

theorem W_fix : ∀ w ∈ F.W, ∀ i ∈ F.O, w i = i := by
  intro w hw i hi
  rw [W_eq] at hw
  exact (fixO i).2 hi w hw

theorem M_le_P : F.M ≤ mclP := by
  change closure (tp 275 '' {x | x ∈ mGens.toArray}) ≤ _
  rw [closure_le]
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ allTbls := by
    have h : T ∈ mGens := by simpa using hT
    change T ∈ eB ++ [gT] ++ mGens ++ sGens ++ cGens
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  exact (tbls_fact.1 T hT').2

theorem card_W : Nat.card F.W = 16 := by
  rw [W_eq, card_eSub]
  norm_num

theorem t0_mem_W : F.t0 ∈ F.W := subset_closure ⟨0, rfl⟩

theorem t0_ne_one : F.t0 ≠ 1 := by
  intro h
  have h2 := mclT0_facts.2.1
  change orderOf F.t0 = 2 at h2
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem card_normP : Nat.card ↥(mclP ⊓ normalizer (F.W : Set (Equiv.Perm (Fin 275)))) ≤ 40320 := by
  have hconj : ∀ g ∈ mclP ⊓ normalizer (F.W : Set (Equiv.Perm (Fin 275))),
      g * F.t0 * g⁻¹ ∈ (F.W : Set (Equiv.Perm (Fin 275))) \ {1} := by
    intro g hg
    refine ⟨(mem_normalizer_iff.mp (Subgroup.mem_inf.mp hg).2 F.t0).mp t0_mem_W, ?_⟩
    intro h1
    apply t0_ne_one
    have h2 : g * F.t0 * g⁻¹ = 1 := h1
    calc F.t0 = g⁻¹ * (g * F.t0 * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  have h1 := CFSG.Quasithin.KGC31.Ru.card_le_of_conj_mem _ F.t0 (Set.toFinite _) hconj
  have hW : (F.W : Set (Equiv.Perm (Fin 275))).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact card_W
  have h15 : ((F.W : Set (Equiv.Perm (Fin 275))) \ {1}).ncard = 15 := by
    rw [Set.ncard_diff_singleton_of_mem (one_mem F.W), hW]
  rw [h15] at h1
  have h2 : Nat.card ↥(mclP ⊓ normalizer (F.W : Set (Equiv.Perm (Fin 275))) ⊓
      centralizer {F.t0}) ≤ 2688 := by
    refine le_trans (Subgroup.card_le_of_le ?_) card_normH
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨hgP, hgN⟩ := Subgroup.mem_inf.mp hg1
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hgP, hg2⟩, hgN⟩
  calc Nat.card ↥(mclP ⊓ normalizer (F.W : Set (Equiv.Perm (Fin 275)))) ≤ 15 * 2688 :=
        h1.trans (Nat.mul_le_mul_left _ h2)
    _ = 40320 := by norm_num

end CertificateChecks.KernelMcLCls

end
