module

public import Certificates.Kernel.HeMult.TabC
public import Certificates.Kernel.HeMult.TabG
public import Certificates.Kernel.HeMult.TabR0
public import Certificates.Kernel.HeMult.TabR1
public import Certificates.Kernel.HeMult.TabR2
public import Certificates.Kernel.He27143.Final
import CFSG.Certificates.Kernel.Spor.VOrbSound

public section

namespace CFSG.KD.HeMult

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KC.HeTab CFSG.KC.HeMult CFSG.KD.HeOrb CFSG.KD.HeTab
  CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Recognition.HeMultiplier

theorem slice_all {p : Nat → Bool} (h : ∀ c < 9, slice p c = true) : ∀ x < 8330, p x = true := by
  intro x hx
  have hs := h (x / 1000) (by omega)
  unfold slice at hs
  have h3 := allN_spec hs (x % 1000) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq] at h3
  have ei : Nat.add (Nat.mul 1000 (x / 1000)) (x % 1000) = x := Nat.div_add_mod x 1000
  rw [ei] at h3
  have hx' : Nat.blt x (nat_lit 8330) = true := by rw [Nat.blt_eq]; exact hx
  exact CFSG.KS.HeVO.bIf_of h3 hx'

theorem famR_all : ∀ c < 9, famR c = true := by
  intro c hc
  interval_cases c
  exacts [R0.all 0 (by norm_num), R0.all 1 (by norm_num), R0.all 2 (by norm_num),
    R1.all 0 (by norm_num), R1.all 1 (by norm_num), R1.all 2 (by norm_num),
    R2.all 0 (by norm_num), R2.all 1 (by norm_num), R2.all 2 (by norm_num)]

theorem c_get {x : Nat} (hx : x < 8330) : r32 CT x = List.foldr (GK AL BE BI) x cW :=
  Nat.eq_of_beq_eq_true (slice_all C.all x hx)

theorem g_get {x : Nat} (hx : x < 8330) :
    powK AL CT Wu U Ui uAC uExp x = true ∧ powK AL CT Wv V Vi vAC vExp x = true ∧
      powK AL CT Ws S Si sAC sExp x = true ∧ tK AL BE BI T Ti tAB x = true := by
  have h := slice_all G.all x hx
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  exact ⟨h1, h2, h3, h4⟩

theorem inv_get {X Xi : Nat → Nat} {x : Nat} (h : invK X Xi x = true) :
    r32 Xi x < 8330 ∧ r32 Xi (r32 X x) = x := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem pow_get {W X Xi : Nat → Nat} {w : List Int} {e x : Nat}
    (h : powK AL CT W X Xi w e x = true) :
    r32 W x = List.foldr (GAC AL CT) x w ∧ r32 X x = itK W e x ∧ r32 Xi x < 8330 ∧
      r32 Xi (r32 X x) = x := by
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, inv_get h3⟩

theorem t_get {X Xi : Nat → Nat} {w : List Int} {x : Nat} (h : tK AL BE BI X Xi w x = true) :
    r32 X x = List.foldr (GK AL BE BI) x w ∧ r32 Xi x < 8330 ∧ r32 Xi (r32 X x) = x := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, inv_get h2⟩

theorem gk_lt (z : Int) {x : Nat} (hx : x < 8330) : GK AL BE BI z x < 8330 :=
  (gens_get z hx).2

theorem foldr_lt (w : List Int) {x : Nat} (hx : x < 8330) : List.foldr (GK AL BE BI) x w < 8330 := by
  induction w with
  | nil => exact hx
  | cons z w ih => exact gk_lt z ih

theorem foldr_acW : ∀ w : List Int, (∀ z ∈ w, z = 1 ∨ z = 3) → ∀ x < 8330,
    List.foldr (GK AL BE BI) x (acW w) = List.foldr (GAC AL CT) x w
  | [], _, _, _ => rfl
  | z :: w, hw, x, hx => by
    have ih := foldr_acW w (fun y hy => hw y (List.mem_cons_of_mem z hy)) x hx
    have e : acW (z :: w) = (if z = 3 then cW else [z]) ++ acW w := by
      simp [acW, List.flatMap_cons]
    rw [e, List.foldr_append, ih, List.foldr_cons]
    have hlt : List.foldr (GAC AL CT) x w < 8330 := by rw [← ih]; exact foldr_lt _ hx
    rcases hw z List.mem_cons_self with rfl | rfl
    · simp only [show ((1 : Int) = 3) = False from by decide, if_false, List.foldr_cons,
        List.foldr_nil]
      rfl
    · simp only [if_true]
      rw [← c_get hlt]
      rfl

theorem itK_succ (W : Nat → Nat) (e x : Nat) : itK W (e + 1) x = r32 W (itK W e x) := rfl

theorem foldr_powW {W : Nat → Nat} {w : List Int}
    (hW : ∀ y < 8330, List.foldr (GK AL BE BI) y w = r32 W y) :
    ∀ e, ∀ x < 8330, List.foldr (GK AL BE BI) x (powW w e) = itK W e x
  | 0, x, _ => rfl
  | e + 1, x, hx => by
    have e1 : powW w (e + 1) = w ++ powW w e := by
      simp [powW, List.replicate_succ, List.flatten_cons]
    rw [e1, List.foldr_append, foldr_powW hW e x hx, itK_succ, ← hW _ (by
      rw [← foldr_powW hW e x hx]; exact foldr_lt _ hx)]

theorem gen_get {k : Nat} {f g : Nat → Nat} (hf : ∀ x < 8330, List.foldr (GK AL BE BI) x
    (heGenWord k) = f x) (hg : ∀ x < 8330, g x < 8330 ∧ g (f x) = x) :
    (heImg OJ k).size = 8330 ∧ (∀ x < 8330, ap (heImg OJ k) x = f x ∧ f x < 8330) ∧
      invOK 8330 (heImg OJ k) (invT 8330 (heImg OJ k)) = true ∧
      ∀ y < 8330, ap (invT 8330 (heImg OJ k)) y = g y := by
  obtain ⟨hs, hw⟩ := CFSG.KS.VO.wordT_ap (n := 8330) (by norm_num) (fun z y hy => gens_get z hy)
    (heGenWord k)
  have ha : ∀ x < 8330, ap (heImg OJ k) x = f x ∧ f x < 8330 := fun x hx => by
    rw [← hf x hx]
    exact hw x hx
  obtain ⟨hi, hv⟩ := CFSG.KS.VO.invT_get (f := f) (g := g) (n := 8330) (by norm_num)
    fun x hx => ⟨(ha x hx).1, (ha x hx).2, (hg x hx).2⟩
  exact ⟨hs, ha, hi, hv⟩

theorem gen0 : (heImg OJ 0).size = 8330 ∧ (∀ x < 8330, ap (heImg OJ 0) x = r32 U x ∧ r32 U x < 8330) ∧
    invOK 8330 (heImg OJ 0) (invT 8330 (heImg OJ 0)) = true ∧
    ∀ y < 8330, ap (invT 8330 (heImg OJ 0)) y = r32 Ui y := by
  have hW : ∀ y < 8330, List.foldr (GK AL BE BI) y (acW uAC) = r32 Wu y := fun y hy => by
    rw [foldr_acW uAC (by decide) y hy, (pow_get (g_get hy).1).1]
  refine gen_get (fun x hx => ?_) (fun x hx => ⟨(pow_get (g_get hx).1).2.2.1, ?_⟩)
  · change List.foldr (GK AL BE BI) x (powW (acW uAC) uExp) = _
    rw [foldr_powW hW uExp x hx, (pow_get (g_get hx).1).2.1]
  · exact (pow_get (g_get hx).1).2.2.2

theorem gen1 : (heImg OJ 1).size = 8330 ∧ (∀ x < 8330, ap (heImg OJ 1) x = r32 V x ∧ r32 V x < 8330) ∧
    invOK 8330 (heImg OJ 1) (invT 8330 (heImg OJ 1)) = true ∧
    ∀ y < 8330, ap (invT 8330 (heImg OJ 1)) y = r32 Vi y := by
  have hW : ∀ y < 8330, List.foldr (GK AL BE BI) y (acW vAC) = r32 Wv y := fun y hy => by
    rw [foldr_acW vAC (by decide) y hy, (pow_get (g_get hy).2.1).1]
  refine gen_get (fun x hx => ?_) (fun x hx => ⟨(pow_get (g_get hx).2.1).2.2.1, ?_⟩)
  · change List.foldr (GK AL BE BI) x (powW (acW vAC) vExp) = _
    rw [foldr_powW hW vExp x hx, (pow_get (g_get hx).2.1).2.1]
  · exact (pow_get (g_get hx).2.1).2.2.2

theorem gen2 : (heImg OJ 2).size = 8330 ∧ (∀ x < 8330, ap (heImg OJ 2) x = r32 S x ∧ r32 S x < 8330) ∧
    invOK 8330 (heImg OJ 2) (invT 8330 (heImg OJ 2)) = true ∧
    ∀ y < 8330, ap (invT 8330 (heImg OJ 2)) y = r32 Si y := by
  have hW : ∀ y < 8330, List.foldr (GK AL BE BI) y (acW sAC) = r32 Ws y := fun y hy => by
    rw [foldr_acW sAC (by decide) y hy, (pow_get (g_get hy).2.2.1).1]
  refine gen_get (fun x hx => ?_) (fun x hx => ⟨(pow_get (g_get hx).2.2.1).2.2.1, ?_⟩)
  · change List.foldr (GK AL BE BI) x (powW (acW sAC) sExp) = _
    rw [foldr_powW hW sExp x hx, (pow_get (g_get hx).2.2.1).2.1]
  · exact (pow_get (g_get hx).2.2.1).2.2.2

theorem gen3 : (heImg OJ 3).size = 8330 ∧ (∀ x < 8330, ap (heImg OJ 3) x = r32 T x ∧ r32 T x < 8330) ∧
    invOK 8330 (heImg OJ 3) (invT 8330 (heImg OJ 3)) = true ∧
    ∀ y < 8330, ap (invT 8330 (heImg OJ 3)) y = r32 Ti y :=
  gen_get (fun x hx => ((t_get (g_get hx).2.2.2).1).symm)
    (fun x hx => ⟨(t_get (g_get hx).2.2.2).2.1, (t_get (g_get hx).2.2.2).2.2⟩)

theorem GL_eq (z : Int) (x : Nat) : CFSG.KC.HeMult.GL U V S T Ui Vi Si Ti z x =
    if z = 1 then r32 U x else if z = 2 then r32 V x else if z = 3 then r32 S x
    else if z = 4 then r32 T x else if z = -1 then r32 Ui x else if z = -2 then r32 Vi x
    else if z = -3 then r32 Si x else r32 Ti x := by
  rcases z with ((_ | _ | _ | _ | _ | k) | (_ | _ | _ | k)) <;> rfl

theorem letter_get {T0 T1 T2 T3 V0 V1 V2 V3 : Table} {f0 f1 f2 f3 g0 g1 g2 g3 : Nat → Nat}
    (h0 : ∀ x < 8330, ap T0 x = f0 x ∧ f0 x < 8330) (h1 : ∀ x < 8330, ap T1 x = f1 x ∧ f1 x < 8330)
    (h2 : ∀ x < 8330, ap T2 x = f2 x ∧ f2 x < 8330) (h3 : ∀ x < 8330, ap T3 x = f3 x ∧ f3 x < 8330)
    (k0 : ∀ x < 8330, ap V0 x = g0 x ∧ g0 x < 8330) (k1 : ∀ x < 8330, ap V1 x = g1 x ∧ g1 x < 8330)
    (k2 : ∀ x < 8330, ap V2 x = g2 x ∧ g2 x < 8330) (k3 : ∀ x < 8330, ap V3 x = g3 x ∧ g3 x < 8330)
    (z : Int) {x : Nat} (hx : x < 8330) :
    ap (heImgLetter T0 T1 T2 T3 V0 V1 V2 V3 z) x =
        (if z = 1 then f0 x else if z = 2 then f1 x else if z = 3 then f2 x
        else if z = 4 then f3 x else if z = -1 then g0 x else if z = -2 then g1 x
        else if z = -3 then g2 x else g3 x) ∧
      (if z = 1 then f0 x else if z = 2 then f1 x else if z = 3 then f2 x
        else if z = 4 then f3 x else if z = -1 then g0 x else if z = -2 then g1 x
        else if z = -3 then g2 x else g3 x) < 8330 := by
  unfold heImgLetter
  split_ifs
  exacts [h0 x hx, h1 x hx, h2 x hx, h3 x hx, k0 x hx, k1 x hx, k2 x hx, k3 x hx]

theorem tab_ext {A B : Table} (hA : A.size = 8330) (hB : B.size = 8330)
    (h : ∀ i < 8330, ap A i = ap B i) : A = B := by
  refine Array.ext (by rw [hA, hB]) fun i h1 h2 => ?_
  have e := h i (by omega)
  unfold ap at e
  rw [getElem!_pos A i h1, getElem!_pos B i h2] at e
  exact UInt32.toNat_inj.mp e

theorem heTab_ok : heTabCheck = true := by
  obtain ⟨s0, a0, i0, v0⟩ := gen0
  obtain ⟨s1, a1, i1, v1⟩ := gen1
  obtain ⟨s2, a2, i2, v2⟩ := gen2
  obtain ⟨s3, a3, i3, v3⟩ := gen3
  have hinvlt : ∀ y < 8330, r32 Ui y < 8330 ∧ r32 Vi y < 8330 ∧ r32 Si y < 8330 ∧
      r32 Ti y < 8330 := fun y hy =>
    ⟨(pow_get (g_get hy).1).2.2.1, (pow_get (g_get hy).2.1).2.2.1,
      (pow_get (g_get hy).2.2.1).2.2.1, (t_get (g_get hy).2.2.2).2.1⟩
  have hL : ∀ z, ∀ x < 8330, ap (heImgLetter (heImg OJ 0) (heImg OJ 1) (heImg OJ 2) (heImg OJ 3)
      (invT 8330 (heImg OJ 0)) (invT 8330 (heImg OJ 1)) (invT 8330 (heImg OJ 2))
      (invT 8330 (heImg OJ 3)) z) x = CFSG.KC.HeMult.GL U V S T Ui Vi Si Ti z x ∧
      CFSG.KC.HeMult.GL U V S T Ui Vi Si Ti z x < 8330 := by
    intro z x hx
    rw [GL_eq]
    exact letter_get a0 a1 a2 a3 (fun y hy => ⟨v0 y hy, (hinvlt y hy).1⟩)
      (fun y hy => ⟨v1 y hy, (hinvlt y hy).2.1⟩) (fun y hy => ⟨v2 y hy, (hinvlt y hy).2.2.1⟩)
      (fun y hy => ⟨v3 y hy, (hinvlt y hy).2.2.2⟩) z hx
  have hW := CFSG.KS.VO.wordT_ap (n := 8330) (by norm_num) hL
  have hR : ∀ x < 8330, relK AL BE U V S T Ui Vi Si Ti heTabRels heSurjA heSurjB x = true :=
    slice_all famR_all
  have hidsz : (idT 8330).size = 8330 := by simp [idT]
  have hasz : OJ.alpha.size = 8330 := by simp [OJ, CFSG.KS.HeVO.vRec]
  have hbsz : OJ.beta.size = 8330 := by simp [OJ, CFSG.KS.HeVO.vRec]
  unfold heTabCheck
  rw [orbitData_eq]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨i0, i1⟩, i2⟩, i3⟩, (fun r hr => ?_)⟩, ?_⟩, ?_⟩
  · refine tab_ext (hW r).1 hidsz fun x hx => ?_
    have h := (bAnd_iff _ _).1 (hR x hx)
    have hr' := Nat.eq_of_beq_eq_true (List.all_eq_true.1 h.1 r hr)
    rw [((hW r).2 x hx).1, hr', idT_ap hx]
  · refine tab_ext (hW _).1 hasz fun x hx => ?_
    have h := (bAnd_iff _ _).1 ((bAnd_iff _ _).1 (hR x hx)).2
    rw [((hW _).2 x hx).1, Nat.eq_of_beq_eq_true h.1, alpha_ap hx]
  · refine tab_ext (hW _).1 hbsz fun x hx => ?_
    have h := (bAnd_iff _ _).1 ((bAnd_iff _ _).1 (hR x hx)).2
    rw [((hW _).2 x hx).1, Nat.eq_of_beq_eq_true h.2, beta_ap hx]

end CFSG.KD.HeMult

end
