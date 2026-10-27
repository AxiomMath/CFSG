module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6RefSFacts
public import Certificates.Kernel.Misc.Sp6RefS.Checks
public import CFSG.Certificates.Kernel.Misc.Sp6RefSSound
public import Certificates.Kernel.Misc.Sp6Transv.Facts
public import Certificates.Certificate8036
public import Certificates.Kernel.Sp62.Final
public import Certificates.Kernel.Sp6A2.Final
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.Certificates.Kernel.Misc.PermClosProof
import CFSG.Certificates.Kernel.Misc.Sp6TransvKit
import CFSG.RankThree.PartTwo.Census.Carrier.G2Three

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6RefS.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62
open CFSG.KD.Sp6RefS (aK aAddK addIdx elt lC distH frameAt commB recAt conjH wordH letH rTabK
  repK)
open CFSG.KC.Misc.Sp6RefS
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS (nGrp repSE repLE Sp6RefSAt Sp6RefSFacts sw01C
  c7Gen0 c7Gen1 c7Gen0Inv c7Gen1Inv l1C c7P r0Gen0 r0Gen1 r0Gen2 r2Gen0 r2Gen1 r4Gen0 r4Gen1)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv (fl0C fl2C)
open CertificateChecks.KernelMisc.Sp6RefS
open CertificateChecks.KernelMisc.Sp6Transv.Facts (emul eq_of_enc enc_one enc_ha enc_hb ha hb)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

theorem mat6_of_enc {g : H6} {c : List ℕ} (hc : canon6 c = true) (h : enc6 g = pk c) :
    mat6 g = dec6 c := by
  rw [← dec6_code6 (mat6 g), pk_inj (canon6_code6 _) hc h]

theorem commB_enc {g h : H6} : commB (enc6 g) (enc6 h) = true ↔ g * h = h * g := by
  rw [commB_iff, ← emul, ← emul]
  exact ⟨fun e => eq_of_enc e, fun e => by rw [e]⟩

theorem conj_of_mul {g x y : H6} (h : g * x = y * g) : g * x * g⁻¹ = y := by
  rw [h, mul_inv_cancel_right]

theorem mem_cen_of {g x : H6} (h : g * x = x * g) : g ∈ Cen x := by
  rw [Cen, Subgroup.mem_centralizer_singleton_iff]
  first | exact h | exact h.symm

theorem comm_of_mem_cen {g x : H6} (h : g ∈ Cen x) : g * x = x * g := by
  rw [Cen, Subgroup.mem_centralizer_singleton_iff] at h
  first | exact h | exact h.symm

theorem P2K_enc (g : H6) : ∀ k, P2K (enc6 g) k = enc6 (g ^ 2 ^ k)
  | 0 => by rw [pow_zero, pow_one]; rfl
  | k + 1 => by
    change MULF (P2K (enc6 g) k) (P2K (enc6 g) k) = _
    rw [P2K_enc g k, ← emul, pow_succ, pow_mul, sq]

theorem two_pow9 {P : Subgroup H6} (hP : IsPGroup 2 P) {g : H6} (hg : g ∈ P) : g ^ 2 ^ 9 = 1 := by
  obtain ⟨m, hm⟩ := hP ⟨g, hg⟩
  have e : g ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  rw [show (2 : ℕ) ^ 9 = 512 from rfl]
  exact pow_512_eq_one e

theorem getD_of_lt {l : List H6} {j : ℕ} (hj : j < l.length) : l.getD j 1 = l[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

structure Hyp (z : Fin 3 → H6) (t f0 f2 sw c0 c1 : H6) : Prop where
  hz : ∀ i, mat6 (z i) = dec6 (zCode i)
  ht : mat6 t = dec6 tCode
  hf0 : mat6 f0 = dec6 fl0C
  hf2 : mat6 f2 = dec6 fl2C
  hsw : mat6 sw = dec6 sw01C
  hc0 : mat6 c0 = dec6 c7Gen0
  hc1 : mat6 c1 = dec6 c7Gen1

variable {z : Fin 3 → H6} {t f0 f2 sw c0 c1 : H6}

theorem Hyp.ez0 (H : Hyp z t f0 f2 sw c0 c1) : enc6 (z 0) = ZG 0 := by
  rw [enc6_of (H.hz 0) (by decide +kernel)]; decide +kernel

theorem Hyp.ez1 (H : Hyp z t f0 f2 sw c0 c1) : enc6 (z 1) = ZG 1 := by
  rw [enc6_of (H.hz 1) (by decide +kernel)]; decide +kernel

theorem Hyp.ez2 (H : Hyp z t f0 f2 sw c0 c1) : enc6 (z 2) = ZG 2 := by
  rw [enc6_of (H.hz 2) (by decide +kernel)]; decide +kernel

theorem Hyp.ez (H : Hyp z t f0 f2 sw c0 c1) (i : Fin 3) : ZG i = enc6 (z i) := by
  match i with
  | 0 => exact H.ez0.symm
  | 1 => exact H.ez1.symm
  | 2 => exact H.ez2.symm

theorem Hyp.et (H : Hyp z t f0 f2 sw c0 c1) : enc6 t = WG 2 := by
  rw [enc6_of H.ht (by decide +kernel)]; decide +kernel

theorem Hyp.ef0 (H : Hyp z t f0 f2 sw c0 c1) : enc6 f0 = WG 0 := by
  rw [enc6_of H.hf0 (by decide +kernel)]; decide +kernel

theorem Hyp.esw (H : Hyp z t f0 f2 sw c0 c1) : enc6 sw = WG 1 := by
  rw [enc6_of H.hsw (by decide +kernel)]; decide +kernel

theorem Hyp.ef2 (H : Hyp z t f0 f2 sw c0 c1) : enc6 f2 = RS 0 := by
  rw [enc6_of H.hf2 (by decide +kernel)]; decide +kernel

theorem Hyp.ec0 (H : Hyp z t f0 f2 sw c0 c1) : enc6 c0 = CG 0 := by
  rw [enc6_of H.hc0 (by decide +kernel)]; decide +kernel

theorem Hyp.ec1 (H : Hyp z t f0 f2 sw c0 c1) : enc6 c1 = CG 1 := by
  rw [enc6_of H.hc1 (by decide +kernel)]; decide +kernel

@[expose] noncomputable def aE (z : Fin 3 → H6) (i : ℕ) : H6 :=
  z 0 ^ (i / 9) * z 1 ^ (i / 3 % 3) * z 2 ^ (i % 3)

theorem Hyp.encA (H : Hyp z t f0 f2 sw c0 c1) {i : ℕ} (hi : i < 27) : AX i = enc6 (aE z i) := by
  have h := aK_sound enc6_enc H.ez sp6refs_a_ok (i / 9) (by omega) (i / 3 % 3) (by omega) (i % 3)
    (by omega)
  rw [show 9 * (i / 9) + 3 * (i / 3 % 3) + i % 3 = i by omega] at h
  exact h

theorem Hyp.t_inv (H : Hyp z t f0 f2 sw c0 c1) : t⁻¹ = t * t :=
  inv_eq_of_mul_eq_one_right (eq_of_enc (by rw [emul, emul, H.et, enc_one]; decide +kernel))

theorem Hyp.z1_eq (H : Hyp z t f0 f2 sw c0 c1) : z 1 = t * z 0 * t⁻¹ :=
  eq_of_enc (by rw [H.t_inv, emul, emul, emul, H.ez1, H.et, H.ez0]; decide +kernel)

theorem Hyp.z2_eq (H : Hyp z t f0 f2 sw c0 c1) : z 2 = t * z 1 * t⁻¹ :=
  eq_of_enc (by rw [H.t_inv, emul, emul, emul, H.ez2, H.et, H.ez1]; decide +kernel)

theorem Hyp.z_mem (H : Hyp z t f0 f2 sw c0 c1) (i : Fin 3) : z i ∈ nGrp z t f0 sw := by
  have h0 : z 0 ∈ nGrp z t f0 sw := Subgroup.subset_closure (by simp)
  have ht : t ∈ nGrp z t f0 sw := Subgroup.subset_closure (by simp)
  have h1 : z 1 ∈ nGrp z t f0 sw := by
    rw [H.z1_eq]
    exact mul_mem (mul_mem ht h0) (inv_mem ht)
  have h2 : z 2 ∈ nGrp z t f0 sw := by
    rw [H.z2_eq]
    exact mul_mem (mul_mem ht h1) (inv_mem ht)
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2

theorem Hyp.aE_mem (H : Hyp z t f0 f2 sw c0 c1) (i : ℕ) : aE z i ∈ nGrp z t f0 sw :=
  mul_mem (mul_mem (pow_mem (H.z_mem 0) _) (pow_mem (H.z_mem 1) _)) (pow_mem (H.z_mem 2) _)

theorem addIdx_lt' : ∀ i < 27, ∀ m < 27, addIdx i m < 27 := by
  decide +kernel

theorem addIdx_lt {i m : ℕ} (hi : i < 27) (hm : m < 27) : addIdx i m < 27 :=
  addIdx_lt' i hi m hm

theorem Hyp.aE_add (H : Hyp z t f0 f2 sw c0 c1) {i m : ℕ} (hi : i < 27) (hm : m < 27) :
    aE z i * aE z m = aE z (addIdx i m) := by
  apply eq_of_enc
  rw [emul, ← H.encA hi, ← H.encA hm, ← H.encA (addIdx_lt hi hm)]
  exact aAdd_sound sp6refs_add_ok i hi m hm

@[expose] noncomputable def wgE (t f0 sw : H6) (s : ℕ) : H6 :=
  if s = 0 then f0 else if s = 1 then sw else t

theorem Hyp.enc_wg (H : Hyp z t f0 f2 sw c0 c1) {s : ℕ} (hs : s < 3) : WG s = enc6 (wgE t f0 sw s) := by
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
  · exact H.ef0.symm
  · exact H.esw.symm
  · exact H.et.symm

theorem Hyp.wg_mem (H : Hyp z t f0 f2 sw c0 c1) (s : ℕ) : wgE t f0 sw s ∈ nGrp z t f0 sw := by
  unfold wgE
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem Hyp.w_ex (H : Hyp z t f0 f2 sw c0 c1) : ∀ j < 48, ∃ g ∈ nGrp z t f0 sw, enc6 g = WX j := by
  obtain ⟨h0, hstep, -⟩ := wK_sound sp6refs_w_ok
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    cases j with
    | zero => exact ⟨1, one_mem _, by rw [enc_one, h0]⟩
    | succ i =>
      obtain ⟨hp, hs, e⟩ := hstep i (by omega)
      obtain ⟨g, hg, eg⟩ := ih (Nat.land (WP i) 255) (by omega) (by omega)
      exact ⟨g * wgE t f0 sw (Nat.shiftRight (WP i) 8), mul_mem hg (H.wg_mem _), by
        rw [emul, eg, ← H.enc_wg hs, e]⟩

theorem elt_eq {i j : ℕ} (hj : j < 48) : elt AX WX (48 * i + j) = MULF (AX i) (WX j) := by
  change MULF (AX ((48 * i + j) / 48)) (WX ((48 * i + j) % 48)) = _
  rw [show (48 * i + j) / 48 = i by omega, show (48 * i + j) % 48 = j by omega]

theorem Hyp.elt_ex (H : Hyp z t f0 f2 sw c0 c1) :
    ∀ n < 1296, ∃ g ∈ nGrp z t f0 sw, enc6 g = elt AX WX n := by
  intro n hn
  obtain ⟨w, hw, ew⟩ := H.w_ex (n % 48) (by omega)
  refine ⟨aE z (n / 48) * w, mul_mem (H.aE_mem _) hw, ?_⟩
  rw [emul, ← H.encA (by omega), ew]
  rfl

theorem Hyp.elt_all (H : Hyp z t f0 f2 sw c0 c1) :
    ∀ g ∈ nGrp z t f0 sw, ∃ n < 1296, enc6 g = elt AX WX n := by
  obtain ⟨-, -, hcl⟩ := wK_sound sp6refs_w_ok
  have key : ∀ g ∈ Submonoid.closure ({z 0, f0, sw, t} : Set H6),
      ∃ n < 1296, enc6 g = elt AX WX n := by
    intro g hg
    induction hg using Submonoid.closure_induction_right with
    | one => exact ⟨0, by omega, by rw [enc_one]; exact (by decide +kernel : ONE = elt AX WX 0)⟩
    | mul_right x _ y hy ih =>
      obtain ⟨n, hn, ex⟩ := ih
      have hi : n / 48 < 27 := by omega
      have hj : n % 48 < 48 := by omega
      have ex' : enc6 x = MULF (AX (n / 48)) (WX (n % 48)) := ex
      have hwgen : ∀ s < 3, y = wgE t f0 sw s → ∃ n < 1296, enc6 (x * y) = elt AX WX n := by
        rintro s hs rfl
        obtain ⟨hlt, he⟩ := hcl (3 * (n % 48) + s) (by omega)
        rw [show (3 * (n % 48) + s) / 3 = n % 48 by omega,
          show (3 * (n % 48) + s) % 3 = s by omega] at he
        obtain ⟨w, -, ew⟩ := H.w_ex (n % 48) hj
        refine ⟨48 * (n / 48) + WC (3 * (n % 48) + s), by omega, ?_⟩
        rw [elt_eq hlt, he, emul, ex', H.encA hi, ← ew, H.enc_wg hs, ← emul, ← emul, ← emul,
          ← emul, mul_assoc]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · obtain ⟨w, -, ew⟩ := H.w_ex (n % 48) hj
        obtain ⟨hm, he⟩ := wm_sound sp6refs_wm_ok (3 * (n % 48)) (by omega)
        rw [show 3 * (n % 48) / 3 = n % 48 by omega, show 3 * (n % 48) % 3 = 0 by omega] at he
        have hwz : w * z 0 = aE z (CertificateChecks.KernelMisc.Sp6RefS.WM (3 * (n % 48))) * w :=
          eq_of_enc (by rw [emul, emul, ew, H.ez0, ← H.encA hm]; exact he)
        have hx : x = aE z (n / 48) * w :=
          eq_of_enc (ex'.trans (by rw [emul, ← H.encA hi, ew]))
        have hlt := addIdx_lt hi hm
        refine ⟨48 * addIdx (n / 48) (WM (3 * (n % 48))) + n % 48, by omega, ?_⟩
        rw [elt_eq hj, hx, mul_assoc, hwz, ← mul_assoc, H.aE_add hi hm, emul, ew,
          ← H.encA hlt]
      · exact hwgen 0 (by omega) (by simp [wgE])
      · exact hwgen 1 (by omega) (by simp [wgE])
      · exact hwgen 2 (by omega) (by simp [wgE])
  intro g hg
  exact key g (by rw [← Subgroup.closure_toSubmonoid_of_finite]; exact hg)

@[expose] noncomputable def lE (z : Fin 3 → H6) (a : ℕ) : H6 :=
  ![z 0, z 0 * z 0, z 1, z 1 * z 1, z 2, z 2 * z 2] ⟨a % 6, Nat.mod_lt _ (by decide)⟩

theorem lC_pk : ∀ a < 6, canon6 (l1C.getD a []) = true ∧ lC ZG a = pk (l1C.getD a []) := by
  decide +kernel

theorem Hyp.enc_lE (H : Hyp z t f0 f2 sw c0 c1) {a : ℕ} (ha : a < 6) : enc6 (lE z a) = lC ZG a := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact H.ez0
  · change enc6 (z 0 * z 0) = _
    rw [emul, H.ez0]; rfl
  · exact H.ez1
  · change enc6 (z 1 * z 1) = _
    rw [emul, H.ez1]; rfl
  · exact H.ez2
  · change enc6 (z 2 * z 2) = _
    rw [emul, H.ez2]; rfl

theorem distH_of : ∀ a < 6, ∀ b < 6, ∀ c < 6, [a / 2, b / 2, c / 2].Nodup → distH a b c = true := by
  decide +kernel

theorem Hyp.frame_conj (H : Hyp z t f0 f2 sw c0 c1) {g : H6} {i : Fin 3} {a : ℕ} (ha : a < 6)
    (h : Nat.beq (MULF (enc6 g) (ZG i)) (MULF (lC ZG a) (enc6 g)) = true) :
    mat6 (g * z i * g⁻¹) = dec6 (l1C.getD a []) := by
  have e : g * z i = lE z a * g :=
    eq_of_enc (by rw [emul, emul, ← H.ez i, H.enc_lE ha]; exact Nat.eq_of_beq_eq_true h)
  rw [conj_of_mul e]
  exact mat6_of_enc (lC_pk a ha).1 ((H.enc_lE ha).trans (lC_pk a ha).2)

theorem Hyp.frames (H : Hyp z t f0 f2 sw c0 c1) :
    ∀ a < 6, ∀ b < 6, ∀ c < 6, [a / 2, b / 2, c / 2].Nodup → ∃ n ∈ nGrp z t f0 sw,
      mat6 (n * z 0 * n⁻¹) = dec6 (l1C.getD a []) ∧ mat6 (n * z 1 * n⁻¹) = dec6 (l1C.getD b []) ∧
        mat6 (n * z 2 * n⁻¹) = dec6 (l1C.getD c []) := by
  intro a ha b hb c hc hnd
  have h := frame_sound sp6refs_frame_ok (36 * a + 6 * b + c) (by omega)
  rw [show (36 * a + 6 * b + c) / 36 = a by omega, show (36 * a + 6 * b + c) / 6 % 6 = b by omega,
    show (36 * a + 6 * b + c) % 6 = c by omega] at h
  obtain ⟨hlt, hf⟩ := h (distH_of a ha b hb c hc hnd)
  obtain ⟨g, hg, eg⟩ := H.elt_ex _ hlt
  rw [← eg] at hf
  simp only [frameAt, Bool.and_eq_true] at hf
  exact ⟨g, hg, H.frame_conj (i := 0) ha hf.1.1, H.frame_conj (i := 1) hb hf.1.2,
    H.frame_conj (i := 2) hc hf.2⟩

theorem Hyp.ew7 (H : Hyp z t f0 f2 sw c0 c1) : enc6 (z 0 * z 1 * z 2) = W7 := by
  rw [emul, emul, H.ez0, H.ez1, H.ez2]; decide +kernel

theorem hG_ab : ∀ l < 2, HG l = enc6 (if l = 0 then ha else hb) := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact (enc_ha.1.trans (by decide +kernel)).symm
  · exact (enc_hb.1.trans (by decide +kernel)).symm

theorem hI_ab : ∀ l < 2, HI l = enc6 (if l = 0 then ha else hb)⁻¹ := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact (enc_ha.2.trans (by decide +kernel)).symm
  · exact (enc_hb.2.trans (by decide +kernel)).symm

theorem card_cen_w7_le {w : H6} (hw : enc6 w = W7) :
    Nat.card (Subgroup.centralizer ({w} : Set H6)) * 2240 ≤ Nat.card H6 := by
  obtain ⟨-, -, ht, hs⟩ := orb_sound sp6refs_orb_ok
  have hc := conj_tree (G := fun l => if l = 0 then ha else hb) (x₀ := w) (N := 2240) (E := OX)
    (PA := OP) (g := HG) (gi := HI) hG_ab hI_ab (by rw [hw]; exact fun k hk => ht k hk)
  have hd := sort_distinct_proved hs
  choose! h hh using hc
  refine CFSG.RankThree.PartTwo.Census.Carrier.G2Three.card_centralizer_mul_le
    (fun k : Fin 2240 => h k * w * (h k)⁻¹) ?_ fun k => ⟨h k, rfl⟩
  intro a b e
  exact Fin.ext (hd a a.2 b b.2 (by rw [hh a a.2, hh b b.2]; exact congrArg enc6 e))

theorem set_pair (a b : H6) : {g | g ∈ [a, b]} = ({a, b} : Set H6) := by
  ext g
  simp

theorem Hyp.c7_facts (H : Hyp z t f0 f2 sw c0 c1) :
    Subgroup.closure {c0, c1} = Cen (z 0 * z 1 * z 2) ∧
      Nat.card (Subgroup.closure ({c0, c1} : Set H6)) = 648 ∧
      ∀ k < 648, ∃ g ∈ Subgroup.closure ({c0, c1} : Set H6), enc6 g = CX k := by
  obtain ⟨h0, h1, ht, hs⟩ := c7_sound sp6refs_c7_ok
  have hG : ∀ j < [c0, c1].length, CG j = enc6 ([c0, c1].getD j 1) := by
    intro j hj
    have hj' : j < 2 := by simpa using hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact H.ec0.symm
    · exact H.ec1.symm
  obtain ⟨hmem, hge, -⟩ := clos_card_proved enc6_enc [c0, c1] hG (by decide) ht hs
  rw [set_pair] at hmem hge
  have hle : Subgroup.closure ({c0, c1} : Set H6) ≤ Cen (z 0 * z 1 * z 2) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact mem_cen_of (commB_enc.mp (by rw [H.ec0, H.ew7]; exact h0))
    · exact mem_cen_of (commB_enc.mp (by rw [H.ec1, H.ew7]; exact h1))
  have hup := card_cen_w7_le H.ew7
  rw [card_H6] at hup
  have hcard : Nat.card (Cen (z 0 * z 1 * z 2)) ≤ Nat.card (Subgroup.closure ({c0, c1} : Set H6)) := by
    change Nat.card (Subgroup.centralizer ({z 0 * z 1 * z 2} : Set H6)) ≤ _
    omega
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  refine ⟨heq, ?_, hmem⟩
  have : Nat.card (Cen (z 0 * z 1 * z 2)) ≤ 648 := by
    change Nat.card (Subgroup.centralizer ({z 0 * z 1 * z 2} : Set H6)) ≤ 648
    omega
  rw [heq] at hge ⊢
  omega

theorem Hyp.c7_table (H : Hyp z t f0 f2 sw c0 c1) :
    (∀ g ∈ Cen (z 0 * z 1 * z 2), ∃ p < 648, enc6 g = CX (CS p)) ∧
      ∀ p < 648, ∃ g ∈ Cen (z 0 * z 1 * z 2), enc6 g = CX (CS p) := by
  obtain ⟨heq, hcard, hmem⟩ := H.c7_facts
  obtain ⟨-, -, -, hs⟩ := c7_sound sp6refs_c7_ok
  rw [← heq]
  have hd := sort_distinct_proved hs
  choose! f hf ef using hmem
  let F : Fin 648 → Subgroup.closure ({c0, c1} : Set H6) := fun k => ⟨f k, hf k k.2⟩
  have hF : Function.Injective F := fun a b e =>
    Fin.ext (hd a a.2 b b.2 ((ef a a.2).symm.trans
      ((congrArg (fun x : Subgroup.closure ({c0, c1} : Set H6) => enc6 x.1) e).trans (ef b b.2))))
  have hbij := hF.bijective_of_nat_card_le
    (by rw [hcard, Nat.card_eq_fintype_card (α := Fin 648), Fintype.card_fin])
  refine ⟨fun g hg => ?_, fun p hp => ?_⟩
  · obtain ⟨k, hk⟩ := hbij.2 ⟨g, hg⟩
    obtain ⟨p, hp, ep⟩ := sort_surj hs k k.2
    refine ⟨p, hp, ?_⟩
    rw [ep]
    exact (congrArg (fun x : Subgroup.closure ({c0, c1} : Set H6) => enc6 x.1) hk).symm.trans
      (ef k k.2)
  · have hlt := (sortAt_spec (hs p hp)).1
    exact ⟨f (CS p), hf _ hlt, ef _ hlt⟩

theorem op_eq {s l : H6} {gens : List H6} {RG RX RP RC TX RR : ℕ → ℕ} {n hi nR e : ℕ}
    (hRG : ∀ j < gens.length, RG j = enc6 (gens.getD j 1)) (hnR : 0 < nR) (hR64 : nR ≤ 64)
    (hG64 : gens.length ≤ 64) (hp : nR = 2 ^ e)
    (htab : rTabK RG RX RP RC gens.length nR (enc6 s) (enc6 l) = true)
    (hrep : repK TX RG RX RR n hi gens.length nR (enc6 s) = true) (hm : n ≤ 64 * hi)
    (hT1 : ∀ g ∈ Cen l, ∃ p < n, enc6 g = TX p) (hT2 : ∀ p < n, ∃ g ∈ Cen l, enc6 g = TX p) :
    Op 2 (Cen s ⊓ Cen l) = Subgroup.closure {g | g ∈ gens} ∧
      Nat.card (Subgroup.closure {g | g ∈ gens}) = nR ∧
      ∀ g ∈ Subgroup.closure {g | g ∈ gens}, ∃ i < nR, enc6 g = RX i := by
  obtain ⟨ht, hc, hs, hcm⟩ := rTab_sound hR64 htab
  obtain ⟨hR1, -, hR3⟩ := clos_card_proved enc6_enc gens hRG hnR ht hs
  obtain ⟨hcard, hall⟩ := hR3 hc
  set R := Subgroup.closure {g | g ∈ gens} with hRdef
  have hRC : R ≤ Cen s ⊓ Cen l := fun g hg => by
    obtain ⟨i, hi, eg⟩ := hall g hg
    have h2 := hcm i hi
    rw [← eg] at h2
    exact Subgroup.mem_inf.mpr ⟨mem_cen_of (commB_enc.mp h2.1), mem_cen_of (commB_enc.mp h2.2)⟩
  have hcs : ∀ {h : H6} {p : ℕ}, h ∈ Cen s → enc6 h = TX p → commB (TX p) (enc6 s) = true :=
    fun hh ep => by rw [← ep]; exact commB_enc.mpr (comm_of_mem_cen hh)
  have hnorm : ∀ h ∈ Cen s ⊓ Cen l, ∀ x ∈ R, h * x * h⁻¹ ∈ R := by
    intro h hh x hx
    obtain ⟨hhs, hhl⟩ := Subgroup.mem_inf.mp hh
    obtain ⟨p, hp, ep⟩ := hT1 h hhl
    have hr := repRec_sound hG64 (rep_sound hm hrep p hp (hcs hhs ep))
    have hgen : ∀ y ∈ {g | g ∈ gens}, h * y * h⁻¹ ∈ R := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
      obtain ⟨i, hi, ei⟩ := hr.1 j hj
      obtain ⟨r, hrR, er⟩ := hR1 i hi
      have e : h * gens[j] = r * h := eq_of_enc (by
        rw [emul, emul, er, ep, ei, hRG j hj, getD_of_lt hj])
      rw [conj_of_mul e]
      exact hrR
    have hmap : R.map (MulAut.conj h).toMonoidHom ≤ R := by
      rw [hRdef, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      exact hgen y hy
    exact hmap ⟨x, hx, rfl⟩
  have hpg : IsPGroup 2 R := IsPGroup.of_card (n := e) (by rw [hcard, hp])
  have h512 : ∀ y ∈ Op 2 (Cen s ⊓ Cen l), P2K (enc6 y) 9 = ONE := fun y hy => by
    rw [P2K_enc, two_pow9 (L41.Op_isPGroup _) hy, enc_one]
  have hle : Op 2 (Cen s ⊓ Cen l) ≤ R := by
    intro x hx
    obtain ⟨hxs, hxl⟩ := Subgroup.mem_inf.mp (L41.Op_le _ hx)
    obtain ⟨p, hp, ep⟩ := hT1 x hxl
    have hr := (repRec_sound hG64 (rep_sound hm hrep p hp (hcs hxs ep))).2
    rw [← ep] at hr
    rcases hr with ⟨i, hi, ei⟩ | hp2 | ⟨a, ha, b, hb, hab, hac, hp2⟩
    · obtain ⟨r, hrR, er⟩ := hR1 i hi
      rwa [eq_of_enc (er.trans ei)] at hrR
    · exact absurd (h512 x hx) hp2
    · obtain ⟨f, hf, ef⟩ := hT2 a ha
      obtain ⟨f', -, ef'⟩ := hT2 b hb
      have hff : f' = f⁻¹ := eq_inv_of_mul_eq_one_right (eq_of_enc (by rw [emul, ef, ef', hab, enc_one]))
      have hfs : f ∈ Cen s := mem_cen_of (commB_enc.mp (by rw [ef]; exact hac))
      have hm' : x * (f * x * f⁻¹) ∈ Op 2 (Cen s ⊓ Cen l) :=
        mul_mem hx (L41.Op_conj_mem (Subgroup.mem_inf.mpr ⟨hfs, hf⟩) hx)
      have hcode : enc6 (x * (f * x * f⁻¹)) = MULF (enc6 x) (MULF (MULF (TX a) (enc6 x)) (TX b)) := by
        rw [emul, emul, emul, ef, ← hff, ef']
      exact absurd (hcode ▸ h512 _ hm') hp2
  exact ⟨le_antisymm hle (L41.le_Op_of_normalized hRC hnorm hpg), hcard, hall⟩

end CertificateChecks.KernelMisc.Sp6RefS.Facts

end
