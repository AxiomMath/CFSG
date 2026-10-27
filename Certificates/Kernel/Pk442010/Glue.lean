module

public import Certificates.Kernel.Pk442010.Checks
public import Certificates.Kernel.Pk442010.ChecksE
public import Certificates.Kernel.Pk442010.ChecksN
public import Certificates.Kernel.Pk442010.ChecksG
public import Certificates.Kernel.Pk442010.ChecksH
public import Certificates.Kernel.A45Cls.Kit
public import Certificates.Kernel.QP45W.Glue
public import CFSG.Certificates.Kernel.Pk442010Sound
public import CFSG.Certificates.Kernel.OrbRow.PRepFacts
public import Certificates.Data.OmegaPkFacts
public import CFSG.Certificates.Kernel.OrbRow.WordRep

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPk442010

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.OrbGroup CFSG.KC.A45Cls
  CFSG.KC.EnumSound CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Sporadic.Schreier
  CFSG.GH74.KGroups
  CFSG.ClassicalInvolution.Q3.TA3.Check Certificates.OmegaPk Subgroup
open CFSG.KC.Pk442010 (homK_spec injK_spec memRK_spec hitK_spec subK_spec centK_spec conjK_spec
  commK_spec nsK_spec prodK_spec eWK_spec eAllK_spec e9K_spec eGK_spec noOddK_spec ord9K_spec
  uK_spec pairK_spec lnK_shift lnK6_div lnK6_mod csAt mulC lnK eL)

local notation "P45" => Equiv.Perm (Fin 45)

local notation "PR" => PRep 45 6

@[expose] def rc (c : ℕ) : P45 := (rhoTab ()).getD c 1

@[expose] def gr (k : ℕ) : P45 :=
  Nat.rec (motive := fun _ => P45) (Certificates.P43Twin.a1 ())
    (fun _ _ => (Certificates.P43Twin.x2 ())⁻¹) k

@[expose] def q1 (j : ℕ) : P45 := (Certificates.P43Twin.Q1 ()).getD j 1

@[expose] def q2 (j : ℕ) : P45 := (Certificates.P43Twin.Q2 ()).getD j 1

@[expose] def cpg (k : ℕ) : P45 := ((cW.getD k []).map KernelA45.gA').prod

@[expose] def cqg (k : ℕ) : P45 := ((cbW.getD k []).map KernelA45.gA').prod

theorem prep_of_beq {L : ℕ} {σ : P45}
    (h : Nat.beq (CFSG.Certificates.Kernel.PkCV.cOf σ).1 L = true) : PR L σ := by
  rw [← Nat.eq_of_beq_eq_true h]
  exact KernelA45.prep_cOf σ

theorem pins' : PR tAL (Certificates.P43Twin.tA ()) ∧ PR tBL (Certificates.P43Twin.tB ()) ∧
    PR g0L (g0 ()) ∧ PR a1L (Certificates.P43Twin.a1 ()) ∧
    PR x2iL (Certificates.P43Twin.x2 ())⁻¹ ∧ (∀ j < 8, PR (rQ1 j) (q1 j)) ∧
    ∀ j < 8, PR (rQ2 j) (q2 j) := by
  have h := pins
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨prep_of_beq h1, prep_of_beq h2, prep_of_beq h3, prep_of_beq h4, prep_of_beq h5,
    fun j hj => prep_of_beq (PK.allN_iff.1 h6 j hj), fun j hj => prep_of_beq (PK.allN_iff.1 h7 j hj)⟩

theorem htA : PR tAL (Certificates.P43Twin.tA ()) := pins'.1

theorem htB : PR tBL (Certificates.P43Twin.tB ()) := pins'.2.1

theorem hg0 : PR g0L (g0 ()) := pins'.2.2.1

theorem gr_prep : ∀ k, PR (rG k) (gr k)
  | 0 => pins'.2.2.2.1
  | _ + 1 => pins'.2.2.2.2.1

theorem foldl_evalW (s t : P45) : ∀ (l : List ℕ) (r : P45),
    (l.map fun k => k != 0).foldl (fun r b => r * if b then t else s) r =
      r * (l.map fun k => Nat.rec (motive := fun _ => P45) s (fun _ _ => t) k).prod
  | [], r => by simp
  | k :: l, r => by
    rw [List.map_cons, List.foldl_cons, foldl_evalW s t l, List.map_cons, List.prod_cons,
      ← mul_assoc]
    cases k <;> rfl

theorem rc_eq {c : ℕ} {l : List ℕ} (hc : c < 81)
    (hl : wordTab.lookup c = some (l.map fun k => k != 0)) : rc c = (l.map gr).prod := by
  unfold rc rhoTab
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range, hl,
    tab_eq]
  change (l.map fun k => k != 0).foldl _ 1 = _
  rw [foldl_evalW, one_mul]
  rfl

theorem dfacts : ∀ i < 24, csAt csW i < 81 ∧
    wordTab.lookup (csAt csW i) = some ((wsR.getD i []).map fun k => k != 0) ∧
    csAt csW i = code ((allSL ()).getD i 1) := by
  intro i hi
  have h := PK.allN_iff.1 codes i hi
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨Nat.blt_eq.mp h.1.1, h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem prep_rR : ∀ i < 24, PR (rR (csAt csW i)) (rc (csAt csW i)) := by
  intro i hi
  have hlen : i < wsR.length := by
    change i < 24
    exact hi
  obtain ⟨-, he⟩ := bindWs_spec words.2.2 i hlen
  simp only [Nat.zero_add] at he
  obtain ⟨h81, hw, -⟩ := dfacts i hi
  rw [List.getD_eq_getElem _ _ hlen] at hw
  rw [he, rc_eq h81 hw]
  exact wordK_prep (by norm_num) (by norm_num) _ fun k _ => gr_prep k

theorem code_mem (A : SL23) : ∃ i < 24, csAt csW i = code A := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 (sl_all.1 A)
  have hi' : i < 24 := sl_all.2 ▸ hi
  refine ⟨i, hi', ?_⟩
  rw [(dfacts i hi').2.2, List.getD_eq_getElem _ _ hi, e]

theorem code_surj {i : ℕ} (hi : i < 24) : ∃ A : SL23, code A = csAt csW i :=
  ⟨_, ((dfacts i hi).2.2).symm⟩

theorem nd (a b : ℕ) : Nat.div a b = a / b := rfl

theorem nm (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem nml (a b : ℕ) : Nat.mul a b = a * b := rfl

theorem na (a b : ℕ) : Nat.add a b = a + b := rfl

theorem digits {a b c d : ℕ} (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3) :
    (27 * a + 9 * b + 3 * c + d) / 27 = a ∧ (27 * a + 9 * b + 3 * c + d) / 9 % 3 = b ∧
      (27 * a + 9 * b + 3 * c + d) / 3 % 3 = c ∧ (27 * a + 9 * b + 3 * c + d) % 3 = d := by
  omega

theorem mulC_code (A B : SL23) : mulC (code A) (code B) = code (A * B) := by
  have hv : ∀ x : ZMod 3, x.val < 3 := fun x => ZMod.val_lt x
  obtain ⟨a1, a2, a3, a4⟩ := digits (hv (A.1 0 0)) (hv (A.1 0 1)) (hv (A.1 1 0)) (hv (A.1 1 1))
  obtain ⟨b1, b2, b3, b4⟩ := digits (hv (B.1 0 0)) (hv (B.1 0 1)) (hv (B.1 1 0)) (hv (B.1 1 1))
  unfold mulC
  simp only [PK.strictN_eq, nd, nm, nml, na, code, a1, a2, a3, a4, b1, b2, b3, b4,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ZMod.val_add,
    ZMod.val_mul]
  omega

theorem rho_mul (A B : SL23) : pkRho (A * B) = pkRho A * pkRho B := by
  obtain ⟨i, hi, ei⟩ := code_mem A
  obtain ⟨j, hj, ej⟩ := code_mem B
  have h := (homK_spec rho.1 prep_rR i hi j hj).2
  rw [ei, ej, mulC_code] at h
  exact h

@[expose] def rhoH : SL23 →* P45 := MonoidHom.mk' pkRho rho_mul

@[expose] def betaH : SL23 →* P45 := (MulAut.conj (g0 ())⁻¹).toMonoidHom.comp rhoH

theorem betaH_apply (A : SL23) : betaH A = cj (g0 ()) (pkRho A) := by
  simp only [betaH, rhoH, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.mk'_apply, inv_inv, cj]

theorem g0_sq : g0 () * g0 () = 1 := (conjK_spec cent.2.2 prep_rR hg0).1

theorem g0_inv : (g0 ())⁻¹ = g0 () := inv_eq_of_mul_eq_one_right g0_sq

theorem prep_rB : ∀ i < 24, PR (rB (csAt csW i)) (cj (g0 ()) (rc (csAt csW i))) := by
  intro i hi
  have h := (conjK_spec cent.2.2 prep_rR hg0).2 i hi
  rw [cj, g0_inv]
  exact h

theorem gA'_P0 {k : ℕ} (hk : k < 2) : KernelA45.gA' k ∈ pkP := by
  change KernelA45.gA' k ∈ QP45.originalSubgroup
  rw [Certificates.Kernel.QP45W.orig_eq]
  refine Subgroup.subset_closure ?_
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, tab_eq]
  interval_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem P0_le_A : pkP ≤ KernelA45.A := by
  change QP45.originalSubgroup ≤ _
  rw [Certificates.Kernel.QP45W.orig_eq, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, tab_eq] at hg
  rcases hg with rfl | rfl
  · exact KernelA45.gA'_mem (k := 0) (by norm_num)
  · exact KernelA45.gA'_mem (k := 1) (by norm_num)

theorem prep_word2 {G : ℕ → ℕ} {ws : List (List ℕ)} (hb : bindWs 45 6 2 KernelA45.KA.G G ws 0 = true)
    {j : ℕ} (hj : j < ws.length) :
    PR (G j) ((ws.getD j []).map KernelA45.gA').prod ∧ ((ws.getD j []).map KernelA45.gA').prod ∈ pkP := by
  obtain ⟨hl, he⟩ := bindWs_spec hb j hj
  rw [Nat.zero_add] at he
  rw [List.getD_eq_getElem _ _ hj, he]
  refine ⟨wordK_prep (by norm_num) (by norm_num) _ fun k hk =>
    KernelA45.prep_gA k (by have := hl k hk; omega), ?_⟩
  refine list_prod_mem fun y hy => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  exact gA'_P0 (hl k hk)

theorem card_inf_cent (s : P45) : Nat.card ↥(pkP ⊓ centralizer ({s} : Set P45)) =
    Nat.card {g : QP45.originalSubgroup // (g : P45) * s = s * g} :=
  Nat.card_congr
    { toFun := fun x => ⟨⟨x, (Subgroup.mem_inf.1 x.2).1⟩,
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2⟩
      invFun := fun g => ⟨g.1, Subgroup.mem_inf.2 ⟨g.1.2,
        Subgroup.mem_centralizer_singleton_iff.2 g.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }


theorem cnt_card (s : P45) :
    Certificates.Kernel.QP45W.cnt s = Nat.card ↥(pkP ⊓ centralizer ({s} : Set P45)) := by
  rw [Certificates.Kernel.QP45W.cnt_eq_card, card_inf_cent]

theorem inv_cls : ∃ a b : P45, ∀ t ∈ pkP, t * t = 1 → t ≠ 1 → ∃ g ∈ pkP,
    (g * t * g⁻¹ = a ∧ Nat.card ↥(pkP ⊓ centralizer ({t} : Set P45)) = 576) ∨
      (g * t * g⁻¹ = b ∧ Nat.card ↥(pkP ⊓ centralizer ({t} : Set P45)) = 96) := by
  obtain ⟨a, b, hab, ha, hb⟩ := Certificates.Kernel.QP45W.reps_eq
  refine ⟨CFSG.Certificates.Kernel.PkCV.ev a, CFSG.Certificates.Kernel.PkCV.ev b,
    fun t ht h2 h1 => ?_⟩
  obtain ⟨g, hg, r, hr, e⟩ := Certificates.Kernel.QP45W.cover ht h2 h1
  rw [hab] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨g, hg, Or.inl ⟨e, ?_⟩⟩
    rw [← cnt_card, ← Certificates.Kernel.QP45W.cnt_conj hg, e,
      Certificates.Kernel.QP45W.cnt_ev]
    exact ha
  · refine ⟨g, hg, Or.inr ⟨e, ?_⟩⟩
    rw [← cnt_card, ← Certificates.Kernel.QP45W.cnt_conj hg, e,
      Certificates.Kernel.QP45W.cnt_ev]
    exact hb

theorem card_inv {t : P45} (ht : t ∈ pkP) (h2 : t * t = 1) (h1 : t ≠ 1) :
    Nat.card ↥(pkP ⊓ centralizer ({t} : Set P45)) = 576 ∨
      Nat.card ↥(pkP ⊓ centralizer ({t} : Set P45)) = 96 := by
  obtain ⟨a, b, h⟩ := inv_cls
  obtain ⟨g, -, h | h⟩ := h t ht h2 h1
  · exact Or.inl h.2
  · exact Or.inr h.2

theorem sq_ne_of_ord {t : P45} (h : orderOf t = 2) : t * t = 1 ∧ t ≠ 1 := by
  refine ⟨by rw [← sq, ← h]; exact pow_orderOf_eq_one t, fun e => ?_⟩
  rw [e, orderOf_one] at h
  exact absurd h (by decide)

theorem ordA : orderOf (Certificates.P43Twin.tA ()) = 2 :=
  (isInvK_iff KernelA45.hn45 htA).1 rho.2.2.2.2.1

theorem ordB : orderOf (Certificates.P43Twin.tB ()) = 2 :=
  (isInvK_iff KernelA45.hn45 htB).1 rho.2.2.2.2.2

theorem cp_facts : ∃ c : ℕ → P45, (∀ i < CP.N, PR (CP.T i) (c i)) ∧ (∀ i < CP.N, c i ∈ pkC) ∧
    (∀ y ∈ pkC, ∃ i < CP.N, c i = y) ∧ (∀ i < CP.N, ∀ j < CP.N, c i = c j → i = j) ∧
    Nat.card pkC = 576 := by
  have h0 : PR (CP.T 0) 1 := by
    rw [ids.1]
    exact prep_pidn (by norm_num) (by norm_num)
  have hgp : ∀ k < 2, PR (CP.G k) (cpg k) ∧ cpg k ∈ pkP := fun k hk => prep_word2 words.1 hk
  obtain ⟨c, hc0, hc, hmem, hcl', hinj⟩ := leftOrb_reps (g := cpg) KernelA45.hn45
    (fun k hk => (hgp k hk).1) CP.cl CP.tr (by decide) h0 KernelA45.ps_lt CP.k
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) (fun _ _ h => h) cpg c
    ⟨0, by decide, hc0⟩ hmem hcl' hinj
  have hle : closure (cpg '' {k | k < 2}) ≤ pkC := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mem_inf.2 ⟨(hgp k hk).2, Subgroup.mem_centralizer_singleton_iff.2
      (KernelA45.comm_of_eq22 (hgp k hk).1 htA (PK.allN_iff.1 gensC.1 k hk))⟩
  have htP : Certificates.P43Twin.tA () ∈ pkP := by
    obtain ⟨i, hi, e⟩ := hitK_spec rho.2.2.2.1
    obtain ⟨m, hm, em⟩ := memRK_spec rho.2.2.1 i hi
    have h1 : c m = Certificates.P43Twin.tA () := prep_unique (hc m hm) (by rw [em, e]; exact htA)
    rw [← h1]
    exact (Subgroup.mem_inf.1 (hle (hmem m hm))).1
  have hC : Nat.card pkC = 576 := by
    have h1 := Subgroup.card_le_of_le hle
    rw [hcard] at h1
    rcases card_inv htP (sq_ne_of_ord ordA).1 (sq_ne_of_ord ordA).2 with h | h
    · exact h
    · change Nat.card pkC = 96 at h
      change CP.N ≤ Nat.card pkC at h1
      rw [h] at h1
      exact absurd h1 (by decide)
  have heq : closure (cpg '' {k | k < 2}) = pkC :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hC, hcard])
  refine ⟨c, hc, fun i hi => hle (hmem i hi), fun y hy => ?_, hinj, hC⟩
  rw [← heq] at hy
  exact hall y hy

theorem cq_facts : ∃ c : ℕ → P45, (∀ i < CQ.N, PR (CQ.T i) (c i)) ∧ (∀ i < CQ.N, c i ∈ pkCB) ∧
    (∀ y ∈ pkCB, ∃ i < CQ.N, c i = y) ∧ Nat.card pkCB = 96 ∧
    Certificates.P43Twin.tB () ∈ pkP := by
  have h0 : PR (CQ.T 0) 1 := by
    rw [ids.2]
    exact prep_pidn (by norm_num) (by norm_num)
  have hgp : ∀ k < 4, PR (CQ.G k) (cqg k) ∧ cqg k ∈ pkP := fun k hk => prep_word2 words.2.1 hk
  obtain ⟨c, hc0, hc, hmem, hcl', hinj⟩ := leftOrb_reps (g := cqg) KernelA45.hn45
    (fun k hk => (hgp k hk).1) CQ.cl CQ.tr (by decide) h0 KernelA45.ps_lt CQ.k
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) (fun _ _ h => h) cqg c
    ⟨0, by decide, hc0⟩ hmem hcl' hinj
  have hle : closure (cqg '' {k | k < 4}) ≤ pkCB := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mem_inf.2 ⟨(hgp k hk).2, Subgroup.mem_centralizer_singleton_iff.2
      (KernelA45.comm_of_eq22 (hgp k hk).1 htB (PK.allN_iff.1 gensC.2 k hk))⟩
  have htP : Certificates.P43Twin.tB () ∈ pkP := by
    obtain ⟨m, hm, em⟩ := memK_spec tBmem
    have h1 : c m = Certificates.P43Twin.tB () := prep_unique (hc m hm) (by rw [em]; exact htB)
    rw [← h1]
    exact (Subgroup.mem_inf.1 (hle (hmem m hm))).1
  have hA : Nat.card ↥(KernelA45.A ⊓ centralizer ({Certificates.P43Twin.tB ()} : Set P45)) = 192 := by
    have := KernelA45.cls_tB.1
    omega
  have hC : Nat.card pkCB = 96 := by
    have h1 := Subgroup.card_le_of_le (inf_le_inf_right (centralizer ({Certificates.P43Twin.tB ()} :
      Set P45)) P0_le_A)
    rw [hA] at h1
    rcases card_inv htP (sq_ne_of_ord ordB).1 (sq_ne_of_ord ordB).2 with h | h
    · change Nat.card pkCB = 576 at h
      change Nat.card pkCB ≤ 192 at h1
      omega
    · exact h
  have heq : closure (cqg '' {k | k < 4}) = pkCB :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hC, hcard])
  refine ⟨c, hc, fun i hi => hle (hmem i hi), fun y hy => ?_, hC, htP⟩
  rw [← heq] at hy
  exact hall y hy

end CertificateChecks.KernelPk442010

end
