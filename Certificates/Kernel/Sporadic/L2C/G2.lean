
module

public import Certificates.Kernel.Sporadic.L2C.G1Base
public import Certificates.Kernel.Sporadic.L2.Vtx
public import CFSG.Sporadic.SuzRecog.LevelTwoCheck
public import CFSG.Sporadic.SuzRecog.ModelGroupsKit
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.L2CG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo
open CFSG.Sporadic.SuzRecog.LevelTwoCover CFSG.Sporadic.SuzRecog.LevelTwoCoverData
open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.ElimCert CFSG.Sporadic.SuzOddCore
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K CertificateChecks.KernelSpor.L2CK
open CertificateChecks.KernelSpor.L2G (sB band bif_true nbeq nblt nble nblt_f nble_f allN_get
  nbr_get nbr_size nbr_high)
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

attribute [local irreducible] volt shift nbr vtab

theorem vt_get {s v : Nat} (hs : s < 2) (hv : v < 2997) : (vtab s)[v]! = VK s v :=
  L2G.vtab_get L2G.vtxOK hs hv

theorem vt_lt {s v : Nat} (hs : s < 2) (hv : v < 2997) : VK s v < 2997 := by
  rw [← vt_get hs hv]
  exact (gens_vset hs hv).1

theorem vt_low {s v : Nat} (hs : s < 2) (hv : v < 2997) : v < 2835 ↔ VK s v < 2835 := by
  rw [← vt_get hs hv]
  exact (gens_vset hs hv).2.1

theorem vt_inj {s v w : Nat} (hs : s < 2) (hv : v < 2997) (hw : w < 2997) (h : VK s v = VK s w) :
    v = w := by
  rw [← vt_get hs hv, ← vt_get hs hw] at h
  have e1 := genElt_smul hs ⟨v, hv⟩
  have e2 := genElt_smul hs ⟨w, hw⟩
  have : genElt s hs • (⟨v, hv⟩ : Fin 2997) = genElt s hs • ⟨w, hw⟩ := by
    rw [e1, e2]
    exact Fin.ext h
  exact congrArg Fin.val (smul_left_cancel _ this)

@[expose] noncomputable def liftV (s u : Nat) : Nat := VK s (u % 2997) + 2997 * ((u / 2997 + shK s (u % 2997)) % 3)

theorem liftArr_eq {s u : Nat} (hs : s < 2) (hu : u < 8991) : (liftArr s)[u]! = liftV s u := by
  rw [liftArr_get hu, vt_get hs (Nat.mod_lt _ (by norm_num)), shift_get hs (Nat.mod_lt _ (by norm_num))]
  rfl

theorem liftV_lt {s u : Nat} (hs : s < 2) : liftV s u < 8991 := by
  have := vt_lt hs (Nat.mod_lt u (by norm_num : 0 < 2997))
  unfold liftV
  omega

theorem liftV_inj {s : Nat} (hs : s < 2) {u w : Nat} (hu : u < 8991) (hw : w < 8991)
    (h : liftV s u = liftV s w) : u = w := by
  have a := vt_lt hs (Nat.mod_lt u (by norm_num : 0 < 2997))
  have b := vt_lt hs (Nat.mod_lt w (by norm_num : 0 < 2997))
  unfold liftV at h
  have e1 : VK s (u % 2997) = VK s (w % 2997) := by omega
  have e2 := vt_inj hs (Nat.mod_lt u (by norm_num)) (Nat.mod_lt w (by norm_num)) e1
  rw [e2] at h
  omega

@[expose] noncomputable def liftE (s : Nat) (hs : s < 2) : Equiv.Perm (Fin 8991) :=
  Equiv.ofBijective (fun u => ⟨liftV s u.1, liftV_lt hs⟩)
    (Finite.injective_iff_bijective.1 fun u w h =>
      Fin.ext (liftV_inj hs u.2 w.2 (congrArg Fin.val h)))

theorem liftE_val {s : Nat} (hs : s < 2) (u : Fin 8991) : (liftE s hs u).1 = liftV s u.1 := rfl

theorem rep_liftE {s : Nat} (hs : s < 2) : Rep 8991 (liftArr s) (liftE s hs) := fun u => by
  rw [liftArr_eq hs u.2, liftE_val]

theorem isInvA_of_rep {n : Nat} {t r : Array Nat} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hr : Rep n r g⁻¹) : isInvA n t r = true := by
  unfold isInvA
  rw [allLt_iff]
  intro i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨ht.lt hi, ?_⟩
  rw [ht.apply hi, hr.apply (g ⟨i, hi⟩).2]
  simp

@[expose] def LiftH : Prop := ∀ x < 2835, liftK x = true

theorem lift_at (H : LiftH) {s : Nat} (hs : s < 2) {x : Nat} (hx : x < 2835) {k : Nat}
    (hk : k < 36) : ∃ j < 36, nbK (VK s x) j = VK s (nbK x k) ∧
      (shK s x + voltK (VK s x) j) % 3 = (voltK x k + shK s (nbK x k)) % 3 := by
  have h := H x hx
  unfold liftK at h
  rw [band] at h
  have h' : liftG VK shK s x = true := by
    interval_cases s
    · exact h.1
    · exact h.2
  unfold liftG at h'
  rw [show Nat.blt x 2835 = true from nblt.2 hx] at h'
  change (strictB (VK s x) fun x' => strictB (L2NB.F x) fun B => strictB (L2CV.F x) fun V =>
    strictB (L2NB.F x') fun B' => strictB (L2CV.F x') fun V' => strictB (shK s x) fun h =>
    allN 36 fun k => strictB (pg 12 (mask 12) B k) fun y => strictB (VK s y) fun y' =>
      strictB (Nat.mod (Nat.add (pg 2 (mask 2) V k) (shK s y)) 3) fun t =>
      anyN 36 fun j => bAnd(Nat.beq (pg 12 (mask 12) B' j) y',
        Nat.beq (Nat.mod (Nat.add h (pg 2 (mask 2) V' j)) 3) t)) = true at h'
  rw [sB, sB, sB, sB, sB, sB] at h'
  have h2 := allN_get h' hk
  rw [sB, sB, sB, anyN_iff] at h2
  obtain ⟨j, hj, e⟩ := h2
  rw [band, nbeq, nbeq] at e
  exact ⟨j, hj, e.1, e.2⟩

theorem coverLiftOK_true (HB : BaseH) (H : LiftH) : coverLiftOK = true := by
  unfold coverLiftOK
  rw [allLt_iff]
  intro s hs
  rw [Bool.and_eq_true]
  refine ⟨isInvA_of_rep (rep_liftE hs) (CFSG.Sporadic.SuzRecog.ModelGroups.rep_invCand
    (rep_liftE hs)), ?_⟩
  unfold presAdj
  rw [allLt_iff]
  intro u hu
  rw [allLt_iff]
  intro k hk
  by_cases hl : u % 2997 < 2835
  · rw [nbrC_size hu hl] at hk
    set x := u % 2997 with hxdef
    set i := u / 2997 with hidef
    have hi : i < 3 := by omega
    have hy := nbK_lt HB hl hk
    obtain ⟨j, hj, e1, e2⟩ := lift_at H hs hl hk
    have hx' := (vt_low hs (by omega)).1 hl
    have hx'2 := vt_lt hs (show x < 2997 by omega)
    have hy'2 := vt_lt hs hy
    rw [nbrC_low hu hl hk, nbC_eq, liftArr_eq hs hu]
    have hw : nbK x k + 2997 * ((i + voltK x k) % 3) < 8991 := by omega
    rw [liftArr_eq hs hw]
    unfold liftV
    have m1 : (nbK x k + 2997 * ((i + voltK x k) % 3)) % 2997 = nbK x k := by omega
    have m2 : (nbK x k + 2997 * ((i + voltK x k) % 3)) / 2997 = (i + voltK x k) % 3 := by omega
    rw [m1, m2, ← hxdef, ← hidef]
    set U := VK s x + 2997 * ((i + shK s x) % 3) with hU
    set W := VK s (nbK x k) + 2997 * (((i + voltK x k) % 3 + shK s (nbK x k)) % 3) with hW
    have hU8 : U < 8991 := by omega
    have hUl : U % 2997 < 2835 := by omega
    have hUm : U % 2997 = VK s x := by omega
    have hUd : U / 2997 = (i + shK s x) % 3 := by omega
    have key : (nbrC[U]!)[j]! = W := by
      rw [nbrC_low hU8 hUl hj, nbC_eq, hUm, hUd, e1, hW]
      omega
    unfold adjB
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true]
    refine ⟨fun e => ?_, Or.inl (occB_iff.2 ⟨j, by rw [nbrC_size hU8 hUl]; exact hj, key⟩)⟩
    have : U % 2997 = W % 2997 := by rw [e]
    rw [hUm, show W % 2997 = VK s (nbK x k) by omega, ← e1] at this
    exact nbK_ne HB hx' hj this.symm
  · rw [nbrC_of_ge hu (by omega)] at hk
    simp at hk

theorem deckArr_get {u : Nat} (hu : u < 8991) : deckArr[u]! = (u + 2997) % 8991 := by
  rw [rep_deck ⟨u, hu⟩, deck_val]

theorem presAdj_deck (HB : BaseH) : presAdj nbrC deckArr = true := by
  unfold presAdj
  rw [allLt_iff]
  intro u hu
  rw [allLt_iff]
  intro k hk
  by_cases hl : u % 2997 < 2835
  · rw [nbrC_size hu hl] at hk
    have hy := nbK_lt HB hl hk
    have hne := nbK_ne HB hl hk
    rw [nbrC_low hu hl hk, nbC_eq, deckArr_get hu]
    have hw : nbK (u % 2997) k + 2997 * ((u / 2997 + voltK (u % 2997) k) % 3) < 8991 := by omega
    rw [deckArr_get hw]
    set U := (u + 2997) % 8991 with hU
    have hU8 : U < 8991 := Nat.mod_lt _ (by norm_num)
    have hUm : U % 2997 = u % 2997 := by omega
    have hUl : U % 2997 < 2835 := by omega
    have key : (nbrC[U]!)[k]! =
        (nbK (u % 2997) k + 2997 * ((u / 2997 + voltK (u % 2997) k) % 3) + 2997) % 8991 := by
      rw [nbrC_low hU8 hUl hk, nbC_eq, hUm]
      omega
    unfold adjB
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true]
    refine ⟨fun e => hne ?_, Or.inl (occB_iff.2 ⟨k, by rw [nbrC_size hU8 hUl]; exact hk, key⟩)⟩
    have := congrArg (· % 2997) e
    omega
  · rw [nbrC_of_ge hu (by omega)] at hk
    simp at hk

theorem p_powA {t : Array Nat} {T : Nat} (ht : P t T) :
    ∀ k, P (powA 1782 t k) (pw T k)
  | 0 => pidn_P
  | k + 1 => p_comp ht (p_powA ht k)

theorem word1782 (h : L2CK.wordK = true) :
    eqA 1782 (powA 1782 (compA 1782 gens[0]! (compA 1782 gens[0]! gens[1]!)) 8) (idA 1782) =
      true := by
  unfold L2CK.wordK at h
  rw [sB] at h
  rw [eqA_P (p_powA (p_comp (L2G.pG (by norm_num)) (p_comp (L2G.pG (by norm_num))
    (L2G.pG (by norm_num)))) 8) pidn_P]
  exact h

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem letK_eq {s v c : Nat} (hv : v < 4096) :
    letK VK shK s (v + 4096 * c) = VK s v + 4096 * (c + shK s v) := by
  unfold letK
  rw [sN, sN]
  have e1 : Nat.land (v + 4096 * c) 4095 = v := by
    change (v + 4096 * c) &&& (2 ^ 12 - 1) = v
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e2 : Nat.shiftRight (v + 4096 * c) 12 = c := by
    change (v + 4096 * c) >>> 12 = c
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [e1, e2]
  change VK s v + (c + shK s v) <<< 12 = _
  rw [Nat.shiftLeft_eq]
  ring

@[expose] def enc (i t : Nat) : Nat := t % 4096 + 2997 * ((i + t / 4096) % 3)

theorem lift_enc {s : Nat} (hs : s < 2) {i v c : Nat} (hv : v < 2997) :
    liftV s (enc i (v + 4096 * c)) = enc i (VK s v + 4096 * (c + shK s v)) := by
  have h1 := vt_lt hs hv
  unfold liftV enc
  have a1 : (v + 4096 * c) % 4096 = v := by omega
  have a2 : (v + 4096 * c) / 4096 = c := by omega
  have b1 : (VK s v + 4096 * (c + shK s v)) % 4096 = VK s v := by omega
  have b2 : (VK s v + 4096 * (c + shK s v)) / 4096 = c + shK s v := by omega
  rw [a1, a2, b1, b2]
  have c1 : (v + 2997 * ((i + c) % 3)) % 2997 = v := by omega
  have c2 : (v + 2997 * ((i + c) % 3)) / 2997 = (i + c) % 3 := by omega
  rw [c1, c2]
  omega

@[expose] noncomputable def wst (x k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => word3 VK shK ih) k

theorem wst_form {x : Nat} (hx : x < 2997) (k : Nat) :
    ∃ v c, v < 2997 ∧ wst x k = v + 4096 * c := by
  induction k with
  | zero => exact ⟨x, 0, hx, by simp [wst]⟩
  | succ k ih =>
    obtain ⟨v, c, hv, e⟩ := ih
    change ∃ v c, v < 2997 ∧ word3 VK shK (wst x k) = v + 4096 * c
    rw [e]
    unfold word3
    rw [letK_eq (by omega), letK_eq (by have := vt_lt (s := 1) (by norm_num) hv; omega),
      letK_eq (by have := vt_lt (s := 0) (by norm_num) (vt_lt (s := 1) (by norm_num) hv); omega)]
    exact ⟨_, _, vt_lt (by norm_num) (vt_lt (by norm_num) (vt_lt (by norm_num) hv)), rfl⟩

@[expose] noncomputable def wE : Equiv.Perm (Fin 8991) :=
  liftE 0 (by norm_num) * (liftE 0 (by norm_num) * liftE 1 (by norm_num))

theorem wE_enc {x : Nat} (hx : x < 2997) {i : Nat} (k : Nat) (w : Fin 8991)
    (hw : w.1 = enc i (wst x k)) : (wE w).1 = enc i (wst x (k + 1)) := by
  obtain ⟨v, c, hv, e⟩ := wst_form hx k
  have h1 := vt_lt (s := 1) (by norm_num) hv
  have h2 := vt_lt (s := 0) (by norm_num) h1
  have hl : (wE w).1 = liftV 0 (liftV 0 (liftV 1 w.1)) := rfl
  rw [hl, hw, e, show wst x (k + 1) = word3 VK shK (wst x k) from rfl, e]
  unfold word3
  rw [letK_eq (by omega), letK_eq (by omega), letK_eq (by omega), lift_enc (s := 1) (by norm_num) hv,
    lift_enc (s := 0) (by norm_num) h1, lift_enc (s := 0) (by norm_num) h2]

@[expose] def WalkH : Prop := ∀ x < 2997, walkK x = true

theorem wE_pow (H : WalkH) : wE ^ 8 = deck := by
  ext u
  set x := u.1 % 2997 with hxd
  set i := u.1 / 2997 with hid
  have hx : x < 2997 := Nat.mod_lt _ (by norm_num)
  have hu := u.2
  have key : ∀ k, ((wE ^ k) u).1 = enc i (wst x k) := by
    intro k
    induction k with
    | zero =>
      change u.1 = enc i x
      unfold enc
      omega
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact wE_enc hx k _ ih
  rw [key 8, deck_val]
  have h := H x hx
  unfold walkK walkG at h
  change strictB (wst x 8) (fun t => bAnd(Nat.beq (Nat.land t 4095) x,
    Nat.beq (Nat.mod (Nat.shiftRight t 12) 3) 1)) = true at h
  obtain ⟨v, c, hv, e⟩ := wst_form hx 8
  rw [sB, e, band, nbeq, nbeq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : Nat.land (v + 4096 * c) 4095 = v := by
    change (v + 4096 * c) &&& (2 ^ 12 - 1) = v
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e2 : Nat.shiftRight (v + 4096 * c) 12 = c := by
    change (v + 4096 * c) >>> 12 = c
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [e1] at h1
  rw [e2] at h2
  change c % 3 = 1 at h2
  rw [e]
  unfold enc
  omega

theorem word8991 (H : WalkH) :
    eqA 8991 (powA 8991 (compA 8991 (liftArr 0) (compA 8991 (liftArr 0) (liftArr 1))) 8) deckArr =
      true :=
  (eqA_iff (rep_powA (rep_compA (rep_liftE (by norm_num)) (rep_compA (rep_liftE (by norm_num))
    (rep_liftE (by norm_num)))) 8) rep_deck).2 (wE_pow H)

theorem coverDeckOK_true (HB : BaseH) (H : WalkH) (hw : L2CK.wordK = true) :
    coverDeckOK = true := by
  unfold coverDeckOK
  rw [presAdj_deck HB, word1782 hw, word8991 H]
  rfl

end CertificateChecks.KernelSpor.L2CG

end
