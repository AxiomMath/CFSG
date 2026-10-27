module

public import Certificates.Kernel.TwistDce3.ON.QAct
public import Certificates.Kernel.TwistDce3.ON.Chain
public import Certificates.Kernel.TwistDce3.ON.CoverTabs
public import Certificates.Kernel.TwistDce3.ON.Walk
public import Certificates.Kernel.ONCover.Glue24320
public import CFSG.Certificates.Kernel.TwistDce2.ChainSound
public import CFSG.Certificates.Kernel.TwistDce3.CoverSound

public section

namespace CFSG.KD.ONDce3

open CFSG.KC.TwDce2 CFSG.KC.TwDce3 CFSG.CosetTable CFSG.Sporadic.Recognition.ONMultiplier
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers CFSG.Certificates.TwDce2.Rels
  CFSG.Certificates.CosetEnumeration CFSG.KC.YModel CFSG.Certificates.TwDce
open CFSG.Certificates.TwDce2 (chainB_sound chainLens)
open CertificateChecks.KernelONCover (card_onCover1_le)
open scoped commutatorElement

abbrev onQ : Type := PG _ onCover1

theorem onS_length : (subsetOf 4 [0, 1, 2]).length = 3 := by decide

theorem rel_act {r : List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)} (hr : r ∈ onCover1) :
    tableHom q_letters_ok (subsetOf 4 [0, 1, 2]).length (FreeGroup.mk r) = 1 := by
  have hr' : r ∈ CertificateChecks.KernelONCover.onCover1U :=
    CertificateChecks.KernelONCover.onCover1_perm.mem_iff.1 hr
  have hc : r.map CFSG.Certificates.TwDce2.Rels.letterCode ∈ onQCodes :=
    List.mem_map.2 ⟨r, hr', rfl⟩
  obtain ⟨-, hfix⟩ := relsOK_sound q_rels_ok q_codes_len _ hc
  refine tableHom_mk_eq_one q_letters_ok q_inv_ok ?_ hfix
  intro l _
  have : l.1.val < 3 := Nat.lt_of_lt_of_eq l.1.isLt onS_length
  omega

noncomputable def onRho : onQ →* (Equiv.Perm (Fin 57))ᵐᵒᵖ :=
  PresentedGroup.toGroup (f := fun j => tableGen q_letters_ok j.val) (by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact rel_act hr)

noncomputable def onPt (q : onQ) (p : ℕ) : ℕ :=
  if h : p < 57 then ((onRho q).unop ⟨p, h⟩).val else p

theorem onPt_of_lt (q : onQ) {p : ℕ} (hp : p < 57) : onPt q p = ((onRho q).unop ⟨p, hp⟩).val :=
  dif_pos hp

theorem onPt_one (p : ℕ) : onPt 1 p = p := by
  by_cases h : p < 57
  · rw [onPt_of_lt _ h, map_one]
    rfl
  · exact dif_neg h

theorem onPt_mul (a b : onQ) (p : ℕ) : onPt (a * b) p = onPt b (onPt a p) := by
  by_cases h : p < 57
  · rw [onPt_of_lt _ h, onPt_of_lt a h, onPt_of_lt _ (Fin.isLt _), map_mul, MulOpposite.unop_mul,
      Equiv.Perm.mul_apply]
  · simp [onPt, h]

theorem j_lt {j : Fin (subsetOf 4 [0, 1, 2]).length} : j.val < 6 := by
  have : j.val < 3 := Nat.lt_of_lt_of_eq j.isLt onS_length
  omega

theorem pt_of (j : Fin (subsetOf 4 [0, 1, 2]).length) {p : ℕ} (hp : p < 57) :
    onPt (PresentedGroup.of j) p = fieldAt 11 (FS (2 * j.val)) p := by
  rw [onPt_of_lt _ hp, onRho, PresentedGroup.toGroup.of]
  exact tableGen_apply q_letters_ok (j_lt (j := j)) ⟨p, hp⟩

theorem pt_of_inv (j : Fin (subsetOf 4 [0, 1, 2]).length) {p : ℕ} (hp : p < 57) :
    onPt (PresentedGroup.of j)⁻¹ p = fieldAt 11 (FS (2 * j.val + 1)) p := by
  rw [onPt_of_lt _ hp, map_inv, onRho, PresentedGroup.toGroup.of]
  exact tableGen_inv_apply q_letters_ok q_inv_ok (j_lt (j := j)) ⟨p, hp⟩

@[expose] def onQGen (c : ℕ) : Fin (subsetOf 4 [0, 1, 2]).length :=
  ⟨[0, 2, 1].getD (c / 2) 0 % 3, Nat.lt_of_lt_of_eq (Nat.mod_lt _ (by norm_num)) onS_length.symm⟩

@[expose] noncomputable def xD (c : ℕ) : onQ :=
  if c < 6 then (if c % 2 = 0 then PresentedGroup.of (onQGen c) else (PresentedGroup.of (onQGen c))⁻¹)
  else 1

theorem hsw : ∀ c < 6, onSw (2 * (onQGen c).val + c % 2) = c := by decide

theorem id_mem : ∀ c < 12, 6 ≤ c → [c] ∈ idCodes := by decide

theorem fb_id {c : ℕ} (hc : c < 12) (h6 : 6 ≤ c) {p : ℕ} (hp : p < 57) :
    fieldAt 11 (FB c) p = p :=
  (relsOK_sound fb_ok.2.1 (by decide) [c] (id_mem c hc h6)).2 p hp

theorem lt_ok : ∀ c < 12, ∀ p < 57, fieldAt 11 (FB c) p < 57 :=
  fun c hc p hp => ((lettersOK_sound fb_ok.1 c hc).2 p hp).1

theorem fb_eq : ∀ c < 12, ∀ p < 57, fieldAt 11 (FB c) p = fieldAt PB (F c) p := by
  intro c hc p hp
  by_cases h6 : c < 6
  · exact CFSG.Certificates.TwDce3.repackOK_sound fb_ok.2.2 c h6 p hp
  · rw [fb_id hc (by omega) hp, f_id_ok c hc (by omega) p hp]

theorem hxD : ∀ c < 12, ∀ p < 57, fieldAt 11 (FB c) p = onPt (xD c) p := by
  intro c hc p hp
  by_cases h6 : c < 6
  · have e : FB c = FS (2 * (onQGen c).val + c % 2) := by rw [FS, hsw c h6]
    rw [e, xD, if_pos h6]
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · rw [if_pos h, pt_of _ hp, h, Nat.add_zero]
    · rw [if_neg (by omega), pt_of_inv _ hp, h]
  · rw [xD, if_neg h6, onPt_one, fb_id hc (by omega) hp]

instance : Finite onQ := card_onCover1_le.1

theorem gens_ok : ∀ c ∈ CFSG.KC.LaneChain.getL CG 0, wBelow 12 (gWord INVM RW c) = true := by
  decide +kernel

theorem lens_ok : ∀ m ∈ chainLens ((gRegs INVM RW (CFSG.KC.LaneChain.getL CG 0)).map
    fun r => CFSG.KC.TwDce.wLen (r / 2)) (getLL CW 0), m < 2 ^ 32 := by
  decide +kernel

theorem base_ok : (∀ i < NB, CFSG.KC.TwDce.fld BS (16 * i) 65535 < 57) ∧
    ∀ b ∈ getLL CB 0, ∃ i < NB,
      CFSG.KC.LaneChain.colDat 11 b / 2 = CFSG.KC.TwDce.fld BS (16 * i) 65535 := by
  decide +kernel

theorem chain_ok : chainB FB 57 (getLL CW 0) (getLL CB 0) (getLL CS 0) (getLL CT 0)
    (gRegs INVM RW (CFSG.KC.LaneChain.getL CG 0)) 1876896 = true := by
  have h := CFSG.Certificates.TwDce3.stabRange_sound stab_ok 0 (by norm_num)
  have e : CFSG.KC.LaneChain.getN CN 0 = 1876896 := by rw [ds_eq.2]; rfl
  rw [Nat.add_zero, e] at h
  exact (CFSG.Certificates.TwDce2.Words.kandB_iff.1 h).2

theorem pt_eq_one {q : onQ} (hq : ∀ i < NB, onPt q (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
    CFSG.KC.TwDce.fld BS (16 * i) 65535) : q = 1 := by
  have hs := chainB_sound (G := onQ) xD onPt onPt_one onPt_mul lt_ok hxD ⊤
    (fun c hc => ⟨gens_ok c hc, Subgroup.mem_top _⟩) lens_ok chain_ok
  rw [Subgroup.card_top] at hs
  have hQ : Nat.card onQ ≤ 1876896 := card_onCover1_le.2
  have : Finite {g : onQ // g ∈ (⊤ : Subgroup onQ) ∧ ∀ b ∈ getLL CB 0,
      onPt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2} :=
    Subtype.finite
  have h1 : Nat.card {g : onQ // g ∈ (⊤ : Subgroup onQ) ∧ ∀ b ∈ getLL CB 0,
      onPt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2} ≤ 1 := by
    omega
  have hsub := Finite.card_le_one_iff_subsingleton.1 h1
  have hmem : ∀ g : onQ, (∀ i < NB, onPt g (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
      CFSG.KC.TwDce.fld BS (16 * i) 65535) → g ∈ (⊤ : Subgroup onQ) ∧ ∀ b ∈ getLL CB 0,
        onPt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2 := by
    intro g hg
    refine ⟨Subgroup.mem_top _, fun b hb => ?_⟩
    obtain ⟨i, hi, he⟩ := base_ok.2 b hb
    rw [he]
    exact hg i hi
  exact congrArg Subtype.val (hsub.elim ⟨q, hmem q hq⟩ ⟨1, hmem 1 fun i _ => onPt_one _⟩)

theorem pt_eval : ∀ (w : List ℕ), (∀ c ∈ w, c < 12) → ∀ p < 57,
    onPt (evalWord xD w) p = w.foldl (fun p c => fieldAt PB (F c) p) p
  | [], _, p, _ => onPt_one p
  | c :: w, hw, p, hp => by
    have hc := hw c List.mem_cons_self
    rw [evalWord_cons, onPt_mul, ← hxD c hc p hp, List.foldl_cons, ← fb_eq c hc p hp]
    exact pt_eval w (fun d hd => hw d (List.mem_cons_of_mem _ hd)) _ (lt_ok c hc p hp)

theorem lift_get_mk {m : ℕ} {rels : Set (FreeGroup (Fin m))} (S : List (Fin m))
    (w : List (Fin S.length × Bool)) :
    FreeGroup.lift (fun j => (PresentedGroup.of (S.get j) : PresentedGroup rels))
      (FreeGroup.mk w) = PresentedGroup.mk rels (FreeGroup.mk (w.map fun l => (S.get l.1, l.2))) := by
  rw [CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk, FreeGroup.lift_mk,
    List.map_map]
  rfl

noncomputable def onPi : onQ →* onPC :=
  PresentedGroup.toGroup (f := fun j => (PresentedGroup.of ((subsetOf 4 [0, 1, 2]).get j) : onPC))
    (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      obtain ⟨u, hu, hur⟩ := List.mem_filterMap.1 hr
      rw [lift_get_mk, map_renumber _ _ _ hur]
      exact PresentedGroup.one_of_mem (List.mem_map_of_mem hu))

theorem get_qgen : ∀ c < 6, (subsetOf 4 [0, 1, 2]).get (onQGen c) = onHGen c := by decide

theorem onPi_xD (c : ℕ) : onPi (xD c) = onX c := by
  by_cases h6 : c < 6
  · rw [xD, onX, if_pos h6, if_pos h6]
    split_ifs
    · rw [onPi, PresentedGroup.toGroup.of]
      exact congrArg (fun g : Fin 4 => (PresentedGroup.of g : onPC)) (get_qgen c h6)
    · rw [map_inv, onPi, PresentedGroup.toGroup.of]
      exact congrArg (fun g : Fin 4 => (PresentedGroup.of g : onPC)⁻¹) (get_qgen c h6)
  · rw [xD, onX, if_neg h6, if_neg h6, map_one]

theorem evalWord_onX (w : List ℕ) : evalWord onX w = onPi (evalWord xD w) := by
  simp only [evalWord, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun c _ => (onPi_xD c).symm

theorem hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
    (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
      CFSG.KC.TwDce.fld BS (16 * i) 65535) → evalWord onX w = 1 := by
  intro w hw hfix
  rw [evalWord_onX, pt_eq_one (q := evalWord xD w) (fun i hi => by
    rw [pt_eval w hw _ (base_ok.1 i hi)]
    exact hfix i hi), map_one]

theorem u3_fix : ∀ i < NB, [0, 0, 0].foldl (fun p c => fieldAt PB (F c) p)
    (CFSG.KC.TwDce.fld BS (16 * i) 65535) = CFSG.KC.TwDce.fld BS (16 * i) 65535 := by
  decide +kernel

theorem y2_fix : ∀ i < NB, [2, 2].foldl (fun p c => fieldAt PB (F c) p)
    (CFSG.KC.TwDce.fld BS (16 * i) 65535) = CFSG.KC.TwDce.fld BS (16 * i) 65535 := by
  decide +kernel

theorem uy7_fix : ∀ i < NB, [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2].foldl
    (fun p c => fieldAt PB (F c) p) (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
      CFSG.KC.TwDce.fld BS (16 * i) 65535 := by
  decide +kernel

noncomputable abbrev onU : onPC := PresentedGroup.of 0

noncomputable abbrev onY : onPC := PresentedGroup.of 2

theorem onX_zero : onX 0 = onU := rfl
theorem onX_two : onX 2 = onY := rfl

theorem u_pow : onU ^ 3 = 1 := by
  have h := hone [0, 0, 0] (by decide) u3_fix
  simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    onX_zero] at h
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  exact h

theorem y_pow : onY ^ 2 = 1 := by
  have h := hone [2, 2] (by decide) y2_fix
  simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    onX_two] at h
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  exact h

theorem uy_pow : (onU * onY) ^ 7 = 1 := by
  have h := hone [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] (by decide) uy7_fix
  simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    onX_zero, onX_two] at h
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  exact h

noncomputable abbrev relEl (r : List (Fin 4 × Bool)) : onPC :=
  PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk} (FreeGroup.mk r)

theorem relEl_one {w : List (Fin 4 × Bool)} (hw : w ∈ onCover) : relEl w = 1 :=
  PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem relEl_comm {r : List (Fin 4 × Bool)} (hr : r ∈ onRels) (i : Fin 4) :
    (PresentedGroup.of i : onPC) * relEl r = relEl r * PresentedGroup.of i := by
  have h : relEl (commWord [(i, true)] r) = 1 := relEl_one (mem_cover₂Words.2 (Or.inl
    (List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_finRange _,
      List.mem_map_of_mem (f := fun r => commWord [(i, true)] r) hr⟩))))
  rw [relEl, mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem relEl_sq {r : List (Fin 4 × Bool)} (hr : r ∈ onRels) : relEl r * relEl r = 1 := by
  have h : relEl (r ++ r) = 1 :=
    relEl_one (mem_cover₂Words.2 (Or.inr (List.mem_map_of_mem (f := fun r => r ++ r) hr)))
  rwa [relEl, ← FreeGroup.mul_mk, map_mul] at h

theorem conj_pow' {G : Type*} [Group G] (t g : G) : ∀ n : ℕ, (t⁻¹ * g * t) ^ n = t⁻¹ * g ^ n * t
  | 0 => by simp
  | n + 1 => by rw [pow_succ, conj_pow' t g n, pow_succ]; group

theorem eq_one_of_sq_odd {G : Type*} [Group G] {a : G} (h2 : a * a = 1) (n : ℕ)
    (hn : a ^ (2 * n + 1) = 1) : a = 1 := by
  rw [pow_succ, pow_mul, sq, h2, one_pow, one_mul] at hn
  exact hn

@[expose] def relA : List (Fin 4 × Bool) := ofCodes [7, 1, 6, 0]

@[expose] def relB : List (Fin 4 × Bool) := ofCodes [7, 5, 6, 5]

theorem relA_mem : relA ∈ onRels := by decide
theorem relB_mem : relB ∈ onRels := by decide

theorem relA_eq : relEl relA = onT⁻¹ * onU⁻¹ * onT * onU := by
  rw [relEl, CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk]
  simp only [relA, ofCodes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_assoc]
  rfl

theorem relB_eq : relEl relB = onT⁻¹ * onY⁻¹ * onT * onY⁻¹ := by
  rw [relEl, CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk]
  simp only [relB, ofCodes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_assoc]
  rfl

theorem conj_u : onT⁻¹ * onU * onT = onU := by
  obtain ⟨a, ha⟩ : ∃ a, a = relEl relA := ⟨_, rfl⟩
  have hs : onT⁻¹ * onU * onT = onU * a⁻¹ := by rw [ha, relA_eq]; group
  have hc : onU * a⁻¹ = a⁻¹ * onU := by
    have := relEl_comm relA_mem 0
    rw [← ha] at this
    calc onU * a⁻¹ = a⁻¹ * (a * onU) * a⁻¹ := by group
      _ = a⁻¹ * (onU * a) * a⁻¹ := by rw [this]
      _ = a⁻¹ * onU := by group
  have h3 : (onU * a⁻¹) ^ 3 = a⁻¹ ^ 3 := by
    rw [(Commute.mul_pow hc 3), u_pow, one_mul]
  have h1 : a⁻¹ ^ 3 = 1 := by
    rw [← h3, ← hs, conj_pow', u_pow]
    group
  have h2 : a⁻¹ * a⁻¹ = 1 := by
    rw [← mul_inv_rev, ha, relEl_sq relA_mem, inv_one]
  have ha1 := eq_one_of_sq_odd h2 1 h1
  rw [hs, ha1, mul_one]

theorem conj_y : onT⁻¹ * onY * onT = onY := by
  obtain ⟨b, hb⟩ : ∃ b, b = relEl relB := ⟨_, rfl⟩
  have hyi : onY⁻¹ = onY := inv_eq_of_mul_eq_one_right (by rw [← pow_two, y_pow])
  have hs : onT⁻¹ * onY * onT = onY * b⁻¹ := by
    have e : onT⁻¹ * onY * onT = onY⁻¹ * b⁻¹ := by rw [hb, relB_eq]; group
    rw [e, hyi]
  have hcu : onU * b⁻¹ = b⁻¹ * onU := by
    have := relEl_comm relB_mem 0
    rw [← hb] at this
    calc onU * b⁻¹ = b⁻¹ * (b * onU) * b⁻¹ := by group
      _ = b⁻¹ * (onU * b) * b⁻¹ := by rw [this]
      _ = b⁻¹ * onU := by group
  have hcy : onY * b⁻¹ = b⁻¹ * onY := by
    have := relEl_comm relB_mem 2
    rw [← hb] at this
    calc onY * b⁻¹ = b⁻¹ * (b * onY) * b⁻¹ := by group
      _ = b⁻¹ * (onY * b) * b⁻¹ := by rw [this]
      _ = b⁻¹ * onY := by group
  have hconj : onT⁻¹ * (onU * onY) * onT = onU * onY * b⁻¹ := by
    calc onT⁻¹ * (onU * onY) * onT = (onT⁻¹ * onU * onT) * (onT⁻¹ * onY * onT) := by group
      _ = onU * onY * b⁻¹ := by rw [conj_u, hs, mul_assoc]
  have hc : (onU * onY) * b⁻¹ = b⁻¹ * (onU * onY) := by
    rw [mul_assoc, hcy, ← mul_assoc, hcu, mul_assoc]
  have h7 : b⁻¹ ^ 7 = 1 := by
    have := conj_pow' onT (onU * onY) 7
    rw [hconj, Commute.mul_pow hc 7, uy_pow, one_mul] at this
    rw [this]
    group
  have h2 : b⁻¹ * b⁻¹ = 1 := by
    rw [← mul_inv_rev, hb, relEl_sq relB_mem, inv_one]
  have hb1 := eq_one_of_sq_odd h2 3 h7
  rw [hs, hb1, mul_one]

theorem comm_of_conj {g : onPC} (h : onT⁻¹ * g * onT = g) : g * onT = onT * g := by
  calc g * onT = onT * (onT⁻¹ * g * onT) := by group
    _ = onT * g := by rw [h]

theorem inv_comm' {g : onPC} (h : g * onT = onT * g) : g⁻¹ * onT = onT * g⁻¹ := by
  calc g⁻¹ * onT = g⁻¹ * (onT * g) * g⁻¹ := by group
    _ = g⁻¹ * (g * onT) * g⁻¹ := by rw [h]
    _ = onT * g⁻¹ := by group

theorem hT : ∀ c < 4, onX c * onT = onT * onX c := by
  intro c hc
  have hu := comm_of_conj conj_u
  have hy := comm_of_conj conj_y
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
  · exact hu
  · exact inv_comm' hu
  · exact hy
  · exact inv_comm' hy

end CFSG.KD.ONDce3

end
