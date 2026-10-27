module

public import Certificates.Kernel.ONCover.Dce.QAct
public import Certificates.Kernel.ONCover.Dce.Chain
public import Certificates.Kernel.ONCover.Dce.CoverTabs
public import Certificates.Kernel.ONCover.Dce.Facts
public import Certificates.Kernel.ONCover.Glue
public import CFSG.Certificates.Kernel.TwistDce2.ChainSound
public import CFSG.Certificates.Kernel.TwistDce3.CoverSound

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce2 CFSG.KC.TwDce3 CFSG.CosetTable CFSG.Sporadic.Recognition.ONMultiplier
  CFSG.LieType.Multipliers CFSG.Certificates.TwDce2.Rels
  CFSG.Certificates.CosetEnumeration CFSG.KC.YModel CFSG.Certificates.TwDce
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover
open CFSG.Certificates.TwDce2 (chainB_sound chainLens)
open CertificateChecks.KernelONCover (card_mainWs₁_le)

abbrev onQ : Type := PG _ mainWs₁

theorem onS_length : (subsetOf 4 [0, 1, 2]).length = 3 := by decide

theorem rel_act {r : List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)} (hr : r ∈ mainWs₁) :
    tableHom q_letters_ok (subsetOf 4 [0, 1, 2]).length (FreeGroup.mk r) = 1 := by
  have hr' : r ∈ CertificateChecks.KernelONCover.mainWs₁U :=
    CertificateChecks.KernelONCover.mainWs₁_perm.mem_iff.1 hr
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

instance : Finite onQ := card_mainWs₁_le.1

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
  have hQ : Nat.card onQ ≤ 1876896 := card_mainWs₁_le.2
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

theorem uy_pow : (onU * onY) ^ 7 = 1 := by
  have h := hone [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] (by decide) uy7_fix
  simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    onX_zero, onX_two] at h
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  exact h

theorem hT : ∀ c < 4, onX c * onT = onT * onX c := hT_of uy_pow

end CFSG.KD.ONCoverDce3

end
