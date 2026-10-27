module

public import Certificates.Kernel.Sporadic.Fi22.Cent17336K
public import Certificates.Kernel.Sporadic.Fi22.Five8124G

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Cent17336

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Fi22Cent
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fv8124
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native

theorem cntN_succ (T : ℕ → ℕ) (n : ℕ) :
    cntN T (n + 1) = cntN T n + if T n = n then 1 else 0 := by
  change Nat.add (cntN T n) (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (T n) n)) = _
  cases h : Nat.beq (T n) n
  · have hne : T n ≠ n := fun e => by
      rw [e, Nat.beq_refl] at h
      exact Bool.noConfusion h
    rw [if_neg hne]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

theorem cntN_eq_card (T : ℕ → ℕ) (n : ℕ) : cntN T n = Nat.card {x : Fin n // T x = x} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i => if T i = i then 1 else 0) n]
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ← ih, cntN_succ]

theorem card_fix_pe {p : ℕ} (hp : PP 3510 12 p) :
    Nat.card {w : Fin 3510 // pe p w = w} = cntN (ev p) 3510 := by
  rw [cntN_eq_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [← pe_apply hp]
  exact ⟨fun e => congrArg Fin.val e, Fin.ext⟩

theorem okDX' : isP D = true ∧ isP X = true ∧ Fi22X.siftP D = true ∧ Fi22X.siftP X = true ∧
    Nat.beq (Fi22X.c D D) idP = true ∧ Nat.beq (pwK X 3) idP = true ∧ Nat.beq X idP = false ∧
    Nat.beq (Fi22X.c (Fi22X.c D X) (Fi22X.c D X)) idP = true ∧ Nat.beq (ev X 0) 1 = true ∧
    Nat.beq (ev X 1) 0 = false ∧ Nat.beq (ev X 1) 1 = false ∧
    Nat.beq (cntN (ev X) 3510) 126 = true := by
  have h := okDX
  simp only [Fv8124.strictB_eq, chkDX, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem pD : PP 3510 12 D := PP_of_isP okDX'.1
theorem pX : PP 3510 12 X := PP_of_isP okDX'.2.1

theorem dArr_eq : CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.dArr () = unpack 3510 12 D := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Fi22C17336T.all 0 (by norm_num)
  rw [← Fi22C17336T.eq] at h
  exact h

theorem xArr_eq : CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.xArr () = unpack 3510 12 X := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Fi22C17336T.all 1 (by norm_num)
  rw [← Fi22C17336T.eq] at h
  exact h

theorem pt_ext {g : Equiv.Perm (Fin 3510)} {a b : Fin 3510} (h : ((g a : Fin 3510) : ℕ) = b) :
    g a = b := Fin.ext h

theorem elt_facts :
    pe D ∈ fi22P ∧ pe X ∈ fi22P ∧ pe D * pe D = 1 ∧ pe X ^ 3 = 1 ∧ pe X ≠ 1 ∧
      (pe D * pe X) * (pe D * pe X) = 1 ∧ pe X 0 = 1 ∧ pe X 1 ≠ 0 ∧ pe X 1 ≠ 1 ∧
      Nat.card {v : Fin 3510 // pe X v = v} = 126 := by
  obtain ⟨-, -, s1, s2, e1, e2, e3, e4, e5, e6, e7, e8⟩ := okDX'
  refine ⟨(mem_P pD).2 s1, (mem_P pX).2 s2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← pe_c pD pD, ← pe_id]
    exact (pe_eq_iff (PP_c pD pD) PP_id).2 e1
  · rw [← pe_pw pX, ← pe_id]
    exact (pe_eq_iff (PP_pw pX 3) PP_id).2 e2
  · rw [← pe_id]
    exact ne_of pX PP_id e3
  · rw [← pe_c pD pX, ← pe_c (PP_c pD pX) (PP_c pD pX), ← pe_id]
    exact (pe_eq_iff (PP_c (PP_c pD pX) (PP_c pD pX)) PP_id).2 e4
  · refine pt_ext ?_
    rw [pe_apply pX]
    exact Nat.eq_of_beq_eq_true e5
  · intro h
    have e : ev X 1 = 0 := by
      have e' := pe_apply pX 1
      rw [h] at e'
      exact e'.symm
    rw [e, Nat.beq_refl] at e6
    exact Bool.noConfusion e6
  · intro h
    have e : ev X 1 = 1 := by
      have e' := pe_apply pX 1
      rw [h] at e'
      exact e'.symm
    rw [e, Nat.beq_refl] at e7
    exact Bool.noConfusion e7
  · rw [card_fix_pe pX]
    exact Nat.eq_of_beq_eq_true e8

theorem strong_pe {j : ℕ} (hj : j < 19) : fi22StrongPerm j = pe (Fi22ChT.F j) := by
  unfold fi22StrongPerm pe
  rw [← fi22StrongArrs_get hj, Fi22X.strong_eq hj]

theorem okS' {j : ℕ} (hj : j < 19) : chkS D X (Fi22ChT.F j) = true := by
  have h := okS
  simp only [Fv8124.strictB_eq] at h
  exact allN_spec' h hj

theorem exists_strong_of_mem {s : Equiv.Perm (Fin 3510)} (hs : s ∈ fi22Chain.strong.toList) :
    ∃ j : ℕ, j < 19 ∧ s = fi22StrongPerm j := by
  rw [Vector.mem_toList_iff, Vector.mem_iff_getElem] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  exact ⟨i, hi, fi22Chain_strong_get ⟨i, hi⟩⟩

theorem base_take_one : fi22Chain.base.toList.take 1 = [(0 : Fin 3510)] := by rfl

theorem base_take_two : fi22Chain.base.toList.take 2 = [(0 : Fin 3510), 1] := by rfl

theorem ev_strong {j : ℕ} (hj : j < 19) (hs : PP 3510 12 (Fi22ChT.F j)) {a : Fin 3510}
    (h : fi22StrongPerm j a = a) : ev (Fi22ChT.F j) a = a := by
  rw [← pe_apply hs, ← strong_pe hj, h]

theorem comm_of_gens {i : ℕ} {c : Equiv.Perm (Fin 3510)}
    (hgen : ∀ s, s ∈ fi22Chain.strong.toList → (∀ b ∈ fi22Chain.base.toList.take i, s b = b) →
      s * c = c * s) : ∀ h ∈ fi22Chain.levelSubgroup i, h * c = c * h := by
  intro h hh
  unfold RawSchreierDatum.levelSubgroup at hh
  induction hh using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨hs1, hs2⟩ := (RawSchreierDatum.mem_levelGenerators_iff _ _ _).1 hs
    exact hgen s hs1 hs2
  | one => simp
  | mul a b _ _ ha hb =>
    calc a * b * c = a * (c * b) := by rw [mul_assoc, hb]
      _ = c * (a * b) := by rw [← mul_assoc, ha, mul_assoc]
  | inv a _ ha =>
    calc a⁻¹ * c = a⁻¹ * (c * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * c) * a⁻¹ := by rw [ha]
      _ = c * a⁻¹ := by group

theorem lev1_comm_d : ∀ h ∈ fi22Chain.levelSubgroup 1, h * pe D = pe D * h := by
  refine comm_of_gens fun s hs1 hs2 => ?_
  obtain ⟨j, hj, rfl⟩ := exists_strong_of_mem hs1
  have h0 : fi22StrongPerm j 0 = 0 := hs2 0 (by rw [base_take_one]; simp)
  have hc := okS' hj
  unfold chkS at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨hp, hd⟩, -⟩ := hc
  have pS := PP_of_isP hp
  have e0 : ev (Fi22ChT.F j) 0 = 0 := ev_strong hj pS h0
  rw [e0, Nat.beq_refl] at hd
  rw [strong_pe hj]
  exact comm_of pS pD (hd.resolve_left Bool.noConfusion)

theorem lev2_comm_x : ∀ h ∈ fi22Chain.levelSubgroup 2, h * pe X = pe X * h := by
  refine comm_of_gens fun s hs1 hs2 => ?_
  obtain ⟨j, hj, rfl⟩ := exists_strong_of_mem hs1
  have h0 : fi22StrongPerm j 0 = 0 := hs2 0 (by rw [base_take_two]; simp)
  have h1 : fi22StrongPerm j 1 = 1 := hs2 1 (by rw [base_take_two]; simp)
  have hc := okS' hj
  unfold chkS at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨hp, -⟩, hx⟩ := hc
  have pS := PP_of_isP hp
  have e0 : ev (Fi22ChT.F j) 0 = 0 := ev_strong hj pS h0
  have e1 : ev (Fi22ChT.F j) 1 = 1 := ev_strong hj pS h1
  rw [e0, e1, Nat.beq_refl, Nat.beq_refl] at hx
  rw [strong_pe hj]
  exact comm_of pS pX (hx.resolve_left Bool.noConfusion)

theorem fi22_hQ :
    ValidSchreier fi22Chain := fi22Chain_valid.1

theorem stab0_comm
    {g : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22P) (h0 : g 0 = 0) : g * pe D = pe D * g := by
  refine lev1_comm_d g ?_
  rw [RawSchreierDatum.mem_levelSubgroup_iff _ fi22_hQ 1 (by decide), base_take_one]
  exact ⟨hg, by simpa using h0⟩

theorem stab01_comm
    {g : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22P) (h0 : g 0 = 0) (h1 : g 1 = 1) :
    g * pe X = pe X * g := by
  refine lev2_comm_x g ?_
  rw [RawSchreierDatum.mem_levelSubgroup_iff _ fi22_hQ 2 (by decide), base_take_two]
  exact ⟨hg, by simp [h0, h1]⟩

theorem gen_pe {k : ℕ} (hk : k < 2) : fi22GenPerm k = pe (Fi22CGT.F k) := by
  unfold fi22GenPerm pe
  rw [Fi22G.gen_eq hk]

theorem gen_mem {k : ℕ} (hk : k < 2) : fi22GenPerm k ∈ fi22P := by
  rw [fi22P, RawSchreierDatum.originalSubgroup]
  refine Subgroup.subset_closure ?_
  change fi22GenPerm k ∈ (Vector.ofFn fun k : Fin 2 => fi22GenPerm k).toList
  rw [Vector.toList_ofFn, List.mem_ofFn]
  exact ⟨⟨k, hk⟩, rfl⟩

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem nIf_beq_zero {p : ℕ} (a b : ℕ) (hp : p = 0) : nIf(Nat.beq p 0, a, b) = a := by
  subst hp
  rfl

theorem nIf_beq_ne {p : ℕ} (a b : ℕ) (hp : p ≠ 0) : nIf(Nat.beq p 0, a, b) = b := by
  rw [beq_false hp]

section Tree

variable (gq : ℕ → Equiv.Perm (Fin 3510)) (par lab : ℕ → ℕ)

@[expose] noncomputable def tQ : ℕ → ℕ → Equiv.Perm (Fin 3510)
  | 0, _ => 1
  | f + 1, p => if p = 0 then 1 else gq (lab p) * tQ f (par p)

theorem tQ_succ {f p : ℕ} (hp : p ≠ 0) : tQ gq par lab (f + 1) p = gq (lab p) * tQ gq par lab f (par p) :=
  if_neg hp

theorem tQ_zero_pt : ∀ f, tQ gq par lab f 0 = 1
  | 0 => rfl
  | _ + 1 => if_pos rfl

variable {gq par lab}

theorem tApp_eqQ {G : ℕ → ℕ → ℕ} (hG : ∀ j (y : Fin 3510), G j y = ((gq j y : Fin 3510) : ℕ)) :
    ∀ (f p : ℕ) (y : Fin 3510), tApp G par lab f p y = ((tQ gq par lab f p y : Fin 3510) : ℕ)
  | 0, _, _ => rfl
  | f + 1, p, y => by
    change nIf(Nat.beq p 0, (y : ℕ), G (lab p) (tApp G par lab f (par p) y)) = _
    by_cases hp : p = 0
    · subst hp
      rw [nIf_beq_zero _ _ rfl, tQ_zero_pt, Equiv.Perm.one_apply]
    · rw [nIf_beq_ne _ _ hp, tApp_eqQ hG f (par p) y, tQ_succ gq par lab hp, Equiv.Perm.mul_apply]
      exact hG _ _

theorem tInv_eqQ {Gi : ℕ → ℕ → ℕ}
    (hG : ∀ j (y : Fin 3510), Gi j y = (((gq j)⁻¹ y : Fin 3510) : ℕ)) :
    ∀ (f p : ℕ) (y : Fin 3510),
      tInv Gi par lab f p y = (((tQ gq par lab f p)⁻¹ y : Fin 3510) : ℕ)
  | 0, _, _ => rfl
  | f + 1, p, y => by
    change nIf(Nat.beq p 0, (y : ℕ), tInv Gi par lab f (par p) (Gi (lab p) y)) = _
    by_cases hp : p = 0
    · subst hp
      rw [nIf_beq_zero _ _ rfl, tQ_zero_pt, inv_one, Equiv.Perm.one_apply]
    ·rw [nIf_beq_ne _ _ hp, hG, tInv_eqQ hG f (par p), tQ_succ gq par lab hp, mul_inv_rev,
        Equiv.Perm.mul_apply]

theorem tQ_mem (hm : ∀ j, gq j ∈ fi22P) : ∀ f p, tQ gq par lab f p ∈ fi22P
  | 0, _ => Subgroup.one_mem _
  | f + 1, p => by
    by_cases hp : p = 0
    · subst hp
      rw [tQ_zero_pt]
      exact Subgroup.one_mem _
    · rw [tQ_succ gq par lab hp]
      exact Subgroup.mul_mem _ (hm _) (tQ_mem hm f (par p))

theorem tQ_zero_aux {dep : ℕ → ℕ}
    (ht : ∀ p < 3510, p ≠ 0 → par p < 3510 ∧ dep (par p) + 1 = dep p ∧
      ∀ h : par p < 3510, ((gq (lab p) ⟨par p, h⟩ : Fin 3510) : ℕ) = p) :
    ∀ (n p : ℕ) (hp : p < 3510), dep p ≤ n → ((tQ gq par lab n p (0 : Fin 3510) : Fin 3510) : ℕ) = p
  | 0, p, hp, hd => by
    by_cases hp0 : p = 0
    · subst hp0
      rfl
    · obtain ⟨-, h3, -⟩ := ht p hp hp0
      omega
  | n + 1, p, hp, hd => by
    by_cases hp0 : p = 0
    · subst hp0
      rw [tQ_zero_pt]
      rfl
    · obtain ⟨h2, h3, h5⟩ := ht p hp hp0
      rw [tQ_succ gq par lab hp0, Equiv.Perm.mul_apply]
      have e : tQ gq par lab n (par p) 0 = ⟨par p, h2⟩ :=
        Fin.ext (tQ_zero_aux ht n (par p) h2 (by omega))
      rw [e]
      exact h5 h2

end Tree

section Gen

variable {a0 a1 d x P0 P1 P2 P3 : ℕ}

@[expose] noncomputable def gQ (a0 a1 j : ℕ) : Equiv.Perm (Fin 3510) :=
  pe (gp a0 a1 (Fi22X.inv a1) j)

theorem pp_of_chkT (hT : chkT a0 a1 (Fi22X.inv a1) P0 P1 P2 = true) :
    PP 3510 12 a0 ∧ PP 3510 12 a1 := by
  rw [chkT.eq_1] at hT
  simp only [Bool.and_eq_true] at hT
  exact ⟨PP_of_isP hT.1.1, PP_of_isP hT.1.2⟩

theorem pGq (h0 : PP 3510 12 a0) (h1 : PP 3510 12 a1) (j : ℕ) :
    PP 3510 12 (gp a0 a1 (Fi22X.inv a1) j) := by
  unfold gp
  cases Nat.beq j 0
  · cases Nat.beq j 1
    · exact PP_inv h1
    · exact h1
  · exact h0

theorem pGiq (h0 : PP 3510 12 a0) (h1 : PP 3510 12 a1) (j : ℕ) :
    PP 3510 12 (gi (Fi22X.inv a0) a1 (Fi22X.inv a1) j) := by
  unfold gi
  cases Nat.beq j 0
  · cases Nat.beq j 1
    · exact h1
    · exact PP_inv h1
  · exact PP_inv h0

theorem giq_pe (h0 : PP 3510 12 a0) (h1 : PP 3510 12 a1) (j : ℕ) :
    pe (gi (Fi22X.inv a0) a1 (Fi22X.inv a1) j) = (gQ a0 a1 j)⁻¹ := by
  unfold gi gQ gp
  cases Nat.beq j 0
  · cases Nat.beq j 1
    · change pe a1 = (pe (Fi22X.inv a1))⁻¹
      rw [pe_inv h1, inv_inv]
    · exact pe_inv h1
  · exact pe_inv h0

theorem gQ_mem (h1 : PP 3510 12 a1) (m0 : pe a0 ∈ fi22P) (m1 : pe a1 ∈ fi22P) (j : ℕ) :
    gQ a0 a1 j ∈ fi22P := by
  unfold gQ gp
  cases Nat.beq j 0
  · cases Nat.beq j 1
    · change pe (Fi22X.inv a1) ∈ fi22P
      rw [pe_inv h1]
      exact Subgroup.inv_mem _ m1
    · exact m1
  · exact m0

theorem tApp_eqG (h0 : PP 3510 12 a0) (h1 : PP 3510 12 a1) (f p : ℕ) (y : Fin 3510) :
    tApp (fun j z => ev (gp a0 a1 (Fi22X.inv a1) j) z) (at12 P0) (at12 P1) f p y =
      ((tQ (gQ a0 a1) (at12 P0) (at12 P1) f p y : Fin 3510) : ℕ) :=
  tApp_eqQ (gq := gQ a0 a1)
    (fun j y => by rw [gQ.eq_1]; exact (pe_apply (pGq h0 h1 j) y).symm) f p y

theorem tInv_eqG (h0 : PP 3510 12 a0) (h1 : PP 3510 12 a1) (f p : ℕ) (y : Fin 3510) :
    tInv (fun j z => ev (gi (Fi22X.inv a0) a1 (Fi22X.inv a1) j) z) (at12 P0) (at12 P1) f p y =
      (((tQ (gQ a0 a1) (at12 P0) (at12 P1) f p)⁻¹ y : Fin 3510) : ℕ) :=
  tInv_eqQ (gq := gQ a0 a1)
    (fun j y => by rw [← giq_pe h0 h1 j]; exact (pe_apply (pGiq h0 h1 j) y).symm) f p y

theorem treeRow_specG (hT : chkT a0 a1 (Fi22X.inv a1) P0 P1 P2 = true) {p : ℕ} (hp : p < 3510)
    (hp0 : p ≠ 0) :
    at12 P1 p < 3 ∧ at12 P0 p < 3510 ∧ at12 P2 (at12 P0 p) + 1 = at12 P2 p ∧ at12 P2 p ≤ 64 ∧
      ev (gp a0 a1 (Fi22X.inv a1) (at12 P1 p)) (at12 P0 p) = p := by
  rw [chkT.eq_1, Bool.and_eq_true] at hT
  have h := allN_spec' hT.2 hp
  rw [treeRow.eq_1, beq_false hp0] at h
  simp only [Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, h4, Nat.eq_of_beq_eq_true h5⟩

theorem tree_hypG (h0 : PP 3510 12 a0) (h1 : PP 3510 12 a1)
    (hT : chkT a0 a1 (Fi22X.inv a1) P0 P1 P2 = true) :
    ∀ p < 3510, p ≠ 0 → at12 P0 p < 3510 ∧ at12 P2 (at12 P0 p) + 1 = at12 P2 p ∧
      ∀ h : at12 P0 p < 3510, ((gQ a0 a1 (at12 P1 p) ⟨at12 P0 p, h⟩ : Fin 3510) : ℕ) = p := by
  intro p hp hp0
  obtain ⟨-, h2, h3, -, h5⟩ := treeRow_specG hT hp hp0
  refine ⟨h2, h3, fun h => ?_⟩
  rw [gQ, pe_apply (pGq h0 h1 _)]
  exact h5

theorem tP_zeroG (h0 : PP 3510 12 a0) (h1 : PP 3510 12 a1)
    (hT : chkT a0 a1 (Fi22X.inv a1) P0 P1 P2 = true) {p : ℕ} (hp : p < 3510) :
    tQ (gQ a0 a1) (at12 P0) (at12 P1) 64 p 0 = ⟨p, hp⟩ := by
  by_cases hp0 : p = 0
  · subst hp0
    rw [tQ_zero_pt]
    exact Fin.ext rfl
  · exact Fin.ext (tQ_zero_aux (tree_hypG h0 h1 hT) 64 p hp (treeRow_specG hT hp hp0).2.2.2.1)

theorem dpF_eqG (h0 : PP 3510 12 a0) (h1 : PP 3510 12 a1) (hd : PP 3510 12 d) (p : ℕ)
    (y : Fin 3510) :
    dpF a0 a1 (Fi22X.inv a0) (Fi22X.inv a1) d P0 P1 p y =
      (((tQ (gQ a0 a1) (at12 P0) (at12 P1) 64 p * pe d *
        (tQ (gQ a0 a1) (at12 P0) (at12 P1) 64 p)⁻¹) y : Fin 3510) : ℕ) := by
  rw [dpF.eq_1, tInv_eqG h0 h1, ← pe_apply hd, tApp_eqG h0 h1, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply]

@[expose] noncomputable def cQ (a0 a1 d x P0 P1 p : ℕ) : Equiv.Perm (Fin 3510) :=
  tQ (gQ a0 a1) (at12 P0) (at12 P1) 64 p * pe d * (tQ (gQ a0 a1) (at12 P0) (at12 P1) 64 p)⁻¹ *
    pe x

theorem step_eqG (h0 : PP 3510 12 a0) (h1 : PP 3510 12 a1) (hd : PP 3510 12 d)
    (hx : PP 3510 12 x) (p : ℕ) (w : Fin 3510) :
    dpF a0 a1 (Fi22X.inv a0) (Fi22X.inv a1) d P0 P1 p (ev x w) =
      ((cQ a0 a1 d x P0 P1 p w : Fin 3510) : ℕ) := by
  rw [cQ.eq_1, Equiv.Perm.mul_apply, ← dpF_eqG h0 h1 hd, pe_apply hx]

theorem sq_ne_oneG (h0 : PP 3510 12 a0) (h1 : PP 3510 12 a1) (hd : PP 3510 12 d)
    (hx : PP 3510 12 x) (hI : chkI a0 a1 (Fi22X.inv a0) (Fi22X.inv a1) d x P0 P1 P3 = true)
    {p : ℕ} (hp : p < 3510) (hp0 : p ≠ 0) (hp1 : p ≠ 1) (hpx : p ≠ ev x 1) :
    cQ a0 a1 d x P0 P1 p * cQ a0 a1 d x P0 P1 p ≠ 1 := by
  rw [chkI.eq_1] at hI
  have h := allN_spec' hI hp
  rw [invRow.eq_1, beq_false hp0, beq_false hp1, beq_false hpx] at h
  simp only [Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  obtain ⟨hw, hne⟩ := h
  obtain ⟨w, hwv⟩ : ∃ w : Fin 3510, (w : ℕ) = at12 P3 p := ⟨⟨_, hw⟩, rfl⟩
  rw [← hwv, step_eqG h0 h1 hd hx, step_eqG h0 h1 hd hx] at hne
  intro hsq
  have e : (cQ a0 a1 d x P0 P1 p * cQ a0 a1 d x P0 P1 p) w = w := by
    rw [hsq, Equiv.Perm.one_apply]
  rw [Equiv.Perm.mul_apply] at e
  rw [e, Nat.beq_refl] at hne
  exact Bool.noConfusion hne

theorem orbit_zeroG (m0 : pe a0 ∈ fi22P) (m1 : pe a1 ∈ fi22P) (hd : PP 3510 12 d)
    (hx : PP 3510 12 x) (hT : chkT a0 a1 (Fi22X.inv a1) P0 P1 P2 = true)
    (hI : chkI a0 a1 (Fi22X.inv a0) (Fi22X.inv a1) d x P0 P1 P3 = true)
    (hcomm : ∀ g ∈ fi22P, g 0 = 0 → g * pe d = pe d * g)
    (hdx : (pe d * pe x) * (pe d * pe x) = 1)
    {g : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22P) (hgx : g * pe x = pe x * g) :
    g 0 = 0 ∨ g 0 = 1 ∨ g 0 = pe x 1 := by
  obtain ⟨h0, h1⟩ := pp_of_chkT hT
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨c0, c1, c2⟩ := hc
  set p : ℕ := (g 0 : ℕ) with hpdef
  have hp : p < 3510 := (g 0).2
  have hp0 : p ≠ 0 := fun e => c0 (Fin.ext e)
  have hp1 : p ≠ 1 := fun e => c1 (Fin.ext e)
  have hpx : p ≠ ev x 1 := fun e => c2 (Fin.ext (e.trans (pe_apply hx 1).symm))
  set t := tQ (gQ a0 a1) (at12 P0) (at12 P1) 64 p with htdef
  have ht0 : t 0 = g 0 := (tP_zeroG h0 h1 hT hp).trans (Fin.eta _ _)
  set h := t⁻¹ * g with hhdef
  have hP : h ∈ fi22P :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (tQ_mem (gQ_mem h1 m0 m1) 64 p)) hg
  have hh0 : h 0 = 0 := by
    rw [hhdef, Equiv.Perm.mul_apply, ← ht0]
    exact Equiv.symm_apply_apply t 0
  have hdc := hcomm h hP hh0
  have hgt : g = t * h := by rw [hhdef, mul_inv_cancel_left]
  have hgd : g * pe d * g⁻¹ = t * pe d * t⁻¹ := by
    rw [hgt]
    calc t * h * pe d * (t * h)⁻¹ = t * (h * pe d) * h⁻¹ * t⁻¹ := by group
      _ = t * (pe d * h) * h⁻¹ * t⁻¹ := by rw [hdc]
      _ = t * pe d * t⁻¹ := by group
  have hxg : pe x * g⁻¹ = g⁻¹ * pe x := by
    calc pe x * g⁻¹ = g⁻¹ * (g * pe x) * g⁻¹ := by group
      _ = g⁻¹ * (pe x * g) * g⁻¹ := by rw [hgx]
      _ = g⁻¹ * pe x := by group
  apply sq_ne_oneG h0 h1 hd hx hI hp hp0 hp1 hpx
  rw [cQ.eq_1, ← htdef, ← hgd]
  calc g * pe d * g⁻¹ * pe x * (g * pe d * g⁻¹ * pe x)
      = g * pe d * (pe x * g⁻¹) * (g * pe d * (pe x * g⁻¹)) := by
        rw [mul_assoc (g * pe d) g⁻¹ (pe x), ← hxg]
    _ = g * ((pe d * pe x) * (pe d * pe x)) * g⁻¹ := by group
    _ = 1 := by rw [hdx]; group

end Gen

theorem pA_mem : pe A0 ∈ fi22P ∧ pe A1 ∈ fi22P := by
  refine ⟨?_, ?_⟩
  · rw [A0, ← gen_pe (k := 0) (by norm_num)]
    exact gen_mem (by norm_num)
  · rw [A1, ← gen_pe (k := 1) (by norm_num)]
    exact gen_mem (by norm_num)

theorem chkT_ok :
    chkT A0 A1 (Fi22X.inv A1) (Fi22CentR.R 0) (Fi22CentR.R 1) (Fi22CentR.R 2) = true := by
  have h := okT
  simp only [Fv8124.strictB_eq] at h
  exact h

theorem chkI_ok : chkI A0 A1 (Fi22X.inv A0) (Fi22X.inv A1) D X (Fi22CentR.R 0) (Fi22CentR.R 1)
    (Fi22CentR.R 3) = true := by
  have h := okI
  simp only [Fv8124.strictB_eq] at h
  exact h

theorem orbit_zero
    {g : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22P) (hgx : g * pe X = pe X * g) :
    g 0 = 0 ∨ g 0 = 1 ∨ g 0 = pe X 1 :=
  orbit_zeroG (a0 := A0) (a1 := A1) (d := D) (x := X) (P0 := Fi22CentR.R 0)
    (P1 := Fi22CentR.R 1) (P2 := Fi22CentR.R 2) (P3 := Fi22CentR.R 3) pA_mem.1 pA_mem.2 pD pX
    chkT_ok chkI_ok (fun _ hg h0 => stab0_comm hg h0) elt_facts.2.2.2.2.2.1 hg hgx

theorem facts :
    ∃ d x : Equiv.Perm (Fin 3510),
      (∀ v : Fin 3510, (CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.dArr ())[(v : ℕ)]! = d v) ∧
      (∀ v : Fin 3510, (CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.xArr ())[(v : ℕ)]! = x v) ∧
      d ∈ fi22P ∧ x ∈ fi22P ∧ d * d = 1 ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ (d * x) * (d * x) = 1 ∧
      x 0 = 1 ∧ x 1 ≠ 0 ∧ x 1 ≠ 1 ∧ Nat.card {v : Fin 3510 // x v = v} = 126 ∧
      (∀ g ∈ fi22P, g 0 = 0 → g * d = d * g) ∧
      (∀ g ∈ fi22P, g 0 = 0 → g 1 = 1 → g * x = x * g) ∧
      (∀ g ∈ fi22P, g * x = x * g → g 0 = 0 ∨ g 0 = 1 ∨ g 0 = x 1) := by
  obtain ⟨m1, m2, e1, e2, e3, e4, e5, e6, e7, e8⟩ := elt_facts
  refine ⟨pe D, pe X, ?_, ?_, m1, m2, e1, e2, e3, e4, e5, e6, e7, e8,
    fun g hg h0 => stab0_comm hg h0, fun g hg h0 h1 => stab01_comm hg h0 h1,
    fun g hg hgx => orbit_zero hg hgx⟩
  · rw [dArr_eq]
    exact rep_pe pD
  · rw [xArr_eq]
    exact rep_pe pX

end CertificateChecks.KernelSpor.Cent17336

end
