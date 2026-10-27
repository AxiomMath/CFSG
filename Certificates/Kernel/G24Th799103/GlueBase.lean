module

public import Certificates.Kernel.G24Th799103.InvChecks
public import Certificates.Kernel.G24Th799103.InvSet
public import Certificates.Kernel.G24Th799103.MChecks
public import Certificates.Kernel.G24Th799103.MSet
public import Certificates.Kernel.G24Th799103.BasicChecks
public import Certificates.Kernel.G24Th799103.GlueChecks
public import Certificates.Kernel.G24Cls.C27204
public import CFSG.Certificates.Kernel.PCentSetCheck
public import CFSG.Certificates.Kernel.PCentSubCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutOuter
import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv
public import CFSG.Sporadic.Co1Block.TwoBComp

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KC.Misc.ArrEnum (pp_of_permB permB)
open CFSG.KC.Misc.HexFlat (hexTable3_sound)
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec21.Holder214Theta
open CFSG.Sporadic.Co1Block (twoBD xBar yBar)
open CertificateChecks.KernelG24.Tri27206
open scoped Pointwise

abbrev Pm := Equiv.Perm (Fin 1365)

theorem g24sz : CFSG.KS.Raw.szOK 1365 11 = true := by quickRfl

theorem band {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem rep_toPerm {p : Nat} (hp : PP 1365 11 p) :
    Rep 1365 (unpack 1365 11 p) (toPerm 1365 11 p) :=
  fun x => by rw [Orb.unpack_get x.2, toPerm_apply hp]

theorem permOfArr_unpack {p : Nat} (hp : PP 1365 11 p) :
    permOfArr 1365 (unpack 1365 11 p) = toPerm 1365 11 p := by
  have h := rep_toPerm hp
  have hc : (∀ i < 1365, (unpack 1365 11 p)[i]! < 1365) ∧
      ∀ i < 1365, ∀ j < 1365, (unpack 1365 11 p)[i]! = (unpack 1365 11 p)[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := (toPerm 1365 11 p).injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [permOfArr, dite_eq_left hc]
  change (unpack 1365 11 p)[(x : ℕ)]! = _
  exact h x

theorem pp_of {p : Nat} (h : permB 1365 11 p = true) : PP 1365 11 p := pp_of_permB g24sz h

theorem toPerm_TG {k : Nat} (hk : k < 13) (hp : PP 1365 11 (TG.F k)) :
    toPerm 1365 11 (TG.F k) = permOfArr 1365 (g24ThArr k) := by
  rw [g24ThArr, TG.eq, hexTable3_sound TG.all k hk, permOfArr_unpack hp]

theorem pp_TG3 : ∀ k < 3, PP 1365 11 (TG.F k) := fun k hk =>
  pp_of (Orb.allN_iff.1 (band ch799103_iperm).1 k hk)

theorem pp_rG : ∀ k < 3, PP 1365 11 (rG k) := fun k hk =>
  pp_of (Orb.allN_iff.1 (band ch799103_iperm).2 k hk)

theorem pp_tau : PP 1365 11 (TG.F 2) := pp_TG3 2 (by norm_num)

theorem toPerm_one : toPerm 1365 11 (pidn 1365 11) = 1 := toPerm_pidn g24sz

theorem toPerm_mulG {x y : Nat} (hx : PP 1365 11 x) (hy : PP 1365 11 y) :
    toPerm 1365 11 (mulG x y) = toPerm 1365 11 x * toPerm 1365 11 y := toPerm_mul hx hy

theorem eq_of_beq {x y : Nat} (h : Nat.beq x y = true) : toPerm 1365 11 x = toPerm 1365 11 y := by
  rw [Nat.eq_of_beq_eq_true h]

theorem ne_of_beq {x y : Nat} (hx : PP 1365 11 x) (hy : PP 1365 11 y)
    (h : (!Nat.beq x y) = true) : toPerm 1365 11 x ≠ toPerm 1365 11 y := fun e => by
  rw [toPerm_injective hx hy e] at h
  simp at h

theorem commPt_iff {x y : Nat} (hx : PP 1365 11 x) (hy : PP 1365 11 y) :
    commPt x y = true ↔ toPerm 1365 11 x * toPerm 1365 11 y = toPerm 1365 11 y * toPerm 1365 11 x := by
  unfold commPt
  rw [Orb.allN_iff]
  constructor
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    simp only [Equiv.Perm.mul_apply, toPerm_apply hx, toPerm_apply hy]
    exact Nat.eq_of_beq_eq_true (h i i.2)
  · intro h i hi
    have e := congrArg (fun g : Pm => (g ⟨i, hi⟩ : Nat)) h
    simp only [Equiv.Perm.mul_apply, toPerm_apply hx, toPerm_apply hy] at e
    rw [Nat.beq_eq]
    exact e

theorem invPt_of {y : Nat} (hy : PP 1365 11 y) (h : toPerm 1365 11 y ^ 2 = 1) : invPt y = true := by
  unfold invPt
  rw [Orb.allN_iff]
  intro i hi
  have e := congrArg (fun g : Pm => (g ⟨i, hi⟩ : Nat)) h
  simp only [sq, Equiv.Perm.mul_apply, toPerm_apply hy, Equiv.Perm.one_apply] at e
  rw [Nat.beq_eq]
  exact e

theorem cube_of_cubePt {x : Nat} (hx : PP 1365 11 x) (h : cubePt x = true) :
    toPerm 1365 11 x ^ 3 = 1 := by
  unfold cubePt at h
  rw [Orb.allN_iff] at h
  refine Equiv.ext fun i => Fin.ext ?_
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, toPerm_apply hx,
    Equiv.Perm.one_apply]
  exact Nat.eq_of_beq_eq_true (h i i.2)

theorem popT_eq (M : Nat) : ∀ m, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => cond (Nat.testBit M i) (Nat.succ acc) acc) m =
      ((Finset.range m).filter fun i => Nat.testBit M i = true).card
  | 0 => by simp
  | m + 1 => by
    change cond (Nat.testBit M m) (Nat.succ (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => cond (Nat.testBit M i) (Nat.succ acc) acc) m)) (Nat.rec (motive := fun _ => Nat)
      (nat_lit 0) (fun i acc => cond (Nat.testBit M i) (Nat.succ acc) acc) m) = _
    rw [popT_eq M m, Finset.range_add_one, Finset.filter_insert]
    by_cases h : Nat.testBit M m = true
    · rw [h, if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      rfl
    · rw [Bool.not_eq_true] at h
      rw [h]
      simp

theorem card_filter_testBit (M : Nat) :
    (Finset.univ.filter fun i : Fin 1365 => Nat.testBit M i = true).card = popK M := by
  unfold popK
  rw [popT_eq, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨hi, h⟩
    exact ⟨⟨i, hi⟩, h, rfl⟩

theorem card_le_of_maps {H : Subgroup Pm} {x : Fin 1365} (S : Finset (Fin 1365))
    (hS : ∀ h ∈ H, h x ∈ S) :
    Nat.card H ≤ S.card * Nat.card (H ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) x : Subgroup Pm) := by
  classical
  set T : Finset Pm := Finset.univ.filter fun g => g ∈ H
  set K : Finset Pm := Finset.univ.filter fun g => g ∈ H ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) x
  have hT : Nat.card H = T.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hK : Nat.card (H ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1365)) x : Subgroup Pm) = K.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hT, hK]
  have hle := Finset.card_le_mul_card_image T K.card (f := fun g => g x) fun a ha => by
    obtain ⟨g₀, hg₀, rfl⟩ := Finset.mem_image.1 ha
    have hg₀H : g₀ ∈ H := (Finset.mem_filter.1 hg₀).2
    refine Finset.card_le_card_of_injOn (fun g => g₀⁻¹ * g) (fun g hg => ?_) ?_
    · obtain ⟨hgT, hgx⟩ := Finset.mem_filter.1 hg
      have hgH : g ∈ H := (Finset.mem_filter.1 hgT).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, Subgroup.mem_inf.2 ⟨H.mul_mem (H.inv_mem hg₀H)
        hgH, MulAction.mem_stabilizer_iff.2 ?_⟩⟩
      rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, hgx]
      simp
    · intro a _ b _ e
      exact mul_left_cancel e
  have himg : (T.image fun g => g x) ⊆ S := fun s hs => by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hs
    exact hS g (Finset.mem_filter.1 hg).2
  calc T.card ≤ K.card * (T.image fun g => g x).card := hle
    _ ≤ K.card * S.card := Nat.mul_le_mul_left _ (Finset.card_le_card himg)
    _ = S.card * K.card := Nat.mul_comm _ _

theorem smul_fix_eq {u g : Pm} (h : u * g = g * u) :
    u • {i : Fin 1365 | g i = i} = {i : Fin 1365 | g i = i} := by
  have hi : u⁻¹ * g = g * u⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_inv_cancel_right]
  ext i
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq, Set.mem_setOf_eq, Equiv.Perm.smul_def]
  constructor
  · intro e
    have := congrArg u e
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, mul_assoc, ← hi, ← mul_assoc,
      mul_inv_cancel, one_mul, ← Equiv.Perm.mul_apply, mul_inv_cancel] at this
    exact this
  · intro e
    rw [← Equiv.Perm.mul_apply, ← hi, Equiv.Perm.mul_apply, e]

theorem ptsM_fixMK {g M : Nat} (hg : PP 1365 11 g) (h : fixMK g M = true) :
    ptsM 1365 M = {i : Fin 1365 | toPerm 1365 11 g i = i} := by
  unfold fixMK at h
  rw [Orb.allN_iff] at h
  ext i
  have e := h i i.2
  have e' : Nat.testBit M i = Nat.beq (pg 11 (mask 11) g i) i := by
    generalize Nat.testBit M i = a at e
    generalize Nat.beq (pg 11 (mask 11) g i) i = b at e
    cases a <;> cases b <;> first | rfl | exact absurd e (by decide)
  simp only [ptsM, Set.mem_setOf_eq]
  rw [e', Nat.beq_eq, ← Fin.val_inj, toPerm_apply hg]


theorem toPerm_eq_of_ptRep {P : Nat} {g : Pm} (hP : PP 1365 11 P) (h : CFSG.KC.G24Key.PtRep P g) :
    toPerm 1365 11 P = g := by
  refine Equiv.ext fun x => Fin.ext ?_
  rw [toPerm_apply hP, ← CertificateChecks.KernelG24.Cls27203.ap_eq_pg]
  exact h x

theorem toPerm_x : toPerm 1365 11 (LC.S 0) = xBar := by
  have h := CertificateChecks.KernelG24.Cls27203.ptLC (j := 0) (by norm_num)
  have e : CFSG.EvenSporadicStandard.G24Aut.gGen 1 0 = xBar := by
    simp [CFSG.EvenSporadicStandard.G24Aut.gGen]
  rw [e] at h
  exact toPerm_eq_of_ptRep (pp_rG 0 (by norm_num)) h

theorem toPerm_y : toPerm 1365 11 (LC.S 1) = yBar := by
  have h := CertificateChecks.KernelG24.Cls27203.ptLC (j := 1) (by norm_num)
  have e : CFSG.EvenSporadicStandard.G24Aut.gGen 1 1 = yBar := by
    simp [CFSG.EvenSporadicStandard.G24Aut.gGen]
  rw [e] at h
  exact toPerm_eq_of_ptRep (pp_rG 1 (by norm_num)) h

theorem mem_D_of_inDK {g : Nat} (hg : PP 1365 11 g) (h : inDK g = true) :
    toPerm 1365 11 g ∈ twoBD := by
  unfold inDK at h
  obtain ⟨hc, hs⟩ := band h
  exact CertificateChecks.KernelG24.Cls27203.mem_of_sift (rep_toPerm hg) hc hs

noncomputable abbrev tau : Pm := toPerm 1365 11 (TG.F 2)

theorem tau_eq : tau = permOfArr 1365 g24ThTau := toPerm_TG (by norm_num) pp_tau

theorem tau_parts : tau * tau = 1 ∧ tau * xBar * tau ∈ twoBD ∧ tau * yBar * tau ∈ twoBD := by
  obtain ⟨h12, h3⟩ := band ch799103_itau
  obtain ⟨h1, h2⟩ := band h12
  have p0 : PP 1365 11 (LC.S 0) := pp_rG 0 (by norm_num)
  have p1 : PP 1365 11 (LC.S 1) := pp_rG 1 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have e := eq_of_beq h1
    rwa [toPerm_mulG pp_tau pp_tau, toPerm_one] at e
  · have m := mem_D_of_inDK (pp_tau.mul (p0.mul pp_tau)) h2
    rwa [toPerm_mul pp_tau (p0.mul pp_tau), toPerm_mul p0 pp_tau, toPerm_x, ← mul_assoc] at m
  · have m := mem_D_of_inDK (pp_tau.mul (p1.mul pp_tau)) h3
    rwa [toPerm_mul pp_tau (p1.mul pp_tau), toPerm_mul p1 pp_tau, toPerm_y, ← mul_assoc] at m

theorem tau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right tau_parts.1

theorem tau_sq : tau ^ 2 = 1 := by rw [sq, tau_parts.1]

theorem tau_conj {g : Pm} (hg : g ∈ twoBD) : tau * g * tau ∈ twoBD := by
  have hn := CFSG.EvenSporadicStandard.G24Aut.mem_normalizer_of_gens (g := tau)
    (by rw [tau_inv]; exact tau_parts.2.1) (by rw [tau_inv]; exact tau_parts.2.2)
  have := (Subgroup.mem_normalizer_iff.1 hn g).1 hg
  rwa [tau_inv] at this

theorem tau_not_mem : tau ∉ twoBD := by
  intro h
  have ha : tau ∈ alternatingGroup (Fin 1365) :=
    CertificateChecks.KernelCo1B.Tri2045.DD_le_alt
      (by rw [← CertificateChecks.KernelG24.Out27204.twoBD_eq_DD]; exact h)
  rw [Equiv.Perm.mem_alternatingGroup,
    CFSG.KC.Pack.sign_of_signK ch799103_bsign fun i => toPerm_apply pp_tau i,
    Odd.neg_one_pow (n := 651) ⟨325, rfl⟩] at ha
  exact absurd ha (by decide)

noncomputable abbrev gR : Subgroup Pm := Subgroup.closure {xBar, yBar, tau}

theorem D_le_R : twoBD ≤ gR := Subgroup.closure_mono (Set.insert_subset_insert (by simp))

theorem tau_mem_R : tau ∈ gR :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem mem_R_cases {g : Pm} (hg : g ∈ gR) : g ∈ twoBD ∨ g * tau ∈ twoBD := by
  have ht := tau_parts.1
  have key : ∀ a b : Pm, a * b = a * tau * (tau * b) := fun a b => by
    rw [mul_assoc a tau, ← mul_assoc tau tau b, ht, one_mul]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact Or.inl (Subgroup.subset_closure (Set.mem_insert _ _))
    · exact Or.inl (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    · exact Or.inr (by rw [ht]; exact twoBD.one_mem)
  | one => exact Or.inl twoBD.one_mem
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (twoBD.mul_mem hx hy)
    · right
      rw [mul_assoc]
      exact twoBD.mul_mem hx hy
    · right
      rw [mul_assoc, key x (y * tau), ← mul_assoc tau y tau]
      exact twoBD.mul_mem hx (tau_conj hy)
    · left
      have e : tau * y = tau * (y * tau) * tau := by
        rw [mul_assoc tau (y * tau) tau, mul_assoc y tau tau, ht, mul_one]
      rw [key x y, e]
      exact twoBD.mul_mem hx (tau_conj hy)
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (twoBD.inv_mem hx)
    · right
      have e : x⁻¹ * tau = tau * (x * tau)⁻¹ * tau := by
        rw [mul_inv_rev, tau_inv, ← mul_assoc tau tau, ht, one_mul]
      rw [e]
      exact tau_conj (twoBD.inv_mem hx)

theorem card_R_le : Nat.card gR ≤ 2 * 251596800 := by
  have ht := tau_parts.1
  have hsub : (gR : Set Pm) ⊆ (twoBD : Set Pm) ∪ (fun g => g * tau) '' (twoBD : Set Pm) := by
    intro g hg
    rcases mem_R_cases hg with h | h
    · exact Or.inl h
    · exact Or.inr ⟨g * tau, h, by dsimp only; rw [mul_assoc, ht, mul_one]⟩
  have hD : (twoBD : Set Pm).ncard = 251596800 := by
    rw [← Nat.card_coe_set_eq]
    exact CFSG.Sporadic.Co1Block.card_twoBD
  calc Nat.card gR = (gR : Set Pm).ncard := Nat.card_coe_set_eq _
    _ ≤ ((twoBD : Set Pm) ∪ (fun g => g * tau) '' (twoBD : Set Pm)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (twoBD : Set Pm).ncard + ((fun g => g * tau) '' (twoBD : Set Pm)).ncard :=
      Set.ncard_union_le _ _
    _ ≤ (twoBD : Set Pm).ncard + (twoBD : Set Pm).ncard :=
      Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
    _ = 2 * 251596800 := by rw [hD]

theorem mem_R_of_inRK {g t : Nat} (hg : PP 1365 11 g) (h : inRK g t = true) :
    toPerm 1365 11 g ∈ gR := by
  unfold inRK at h
  cases e : Nat.beq t 0 <;> rw [e] at h
  · rw [cond_false] at h
    have hm := mem_D_of_inDK (hg.mul pp_tau) h
    rw [toPerm_mul hg pp_tau] at hm
    have := gR.mul_mem (D_le_R hm) tau_mem_R
    rwa [mul_assoc, tau_parts.1, mul_one] at this
  · rw [cond_true] at h
    exact D_le_R (mem_D_of_inDK hg h)

end CertificateChecks.KernelG24Th

end
