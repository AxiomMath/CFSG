module

public import Certificates.Kernel.HN1408.Tab4BlkChk
public import Certificates.Kernel.HN1408.Tab4CntFacts
public import Certificates.Kernel.HN1408.BlockAct
public import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CbT

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KD.HN1408 CFSG.KD.HN1408.Tr2
open CFSG.KD.HN1408.BlockAct CFSG.KD.HN1408.Tab4Blk
open CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.Section3Model CFSG.EvenSporadicStandard.HNRecog.Section3

noncomputable def finPt (R : Nat → Nat) (k : Nat) : Fin 1408 :=
  if h : R k < 1408 then ⟨R k, h⟩ else 0

theorem finPt_eq {R : Nat → Nat} {k : Nat} (h : R k < 1408) : finPt R k = ⟨R k, h⟩ := by
  rw [finPt, dif_pos h]

theorem finPt_val {R : Nat → Nat} {k : Nat} (h : R k < 1408) : (finPt R k).val = R k := by
  rw [finPt_eq h]

theorem tabK_parts {L D P R : Nat → Nat} {nD n : Nat} (h : tabK L D P R nD n = true) :
    (∀ x < 1408, L x ≠ 0 → P x < nD ∧ D (P x) = x) ∧
      (∀ d < nD, D d < 1408 ∧ L (D d) ≠ 0 ∧ L (D d) ≤ n) ∧
      (∀ k < n, R k < 1408 ∧ L (R k) = k + 1) := by
  unfold tabK at h
  obtain ⟨h1, h⟩ := mkA h
  obtain ⟨h2, h3⟩ := mkA h
  refine ⟨fun x hx hL => ?_, fun d hd => ?_, fun k hk => ?_⟩
  · have e := allN_spec h1 x hx
    have e0 : Nat.beq (L x) 0 = false := Bool.eq_false_iff.2 fun h'' => hL (Nat.eq_of_beq_eq_true h'')
    rw [e0] at e
    obtain ⟨a, b⟩ := mkA e
    exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩
  · obtain ⟨a, e⟩ := mkA (allN_spec h2 d hd)
    obtain ⟨b, c⟩ := mkA e
    refine ⟨Nat.blt_eq.mp a, fun e0 => ?_, Nat.le_of_ble_eq_true c⟩
    rw [e0] at b
    exact Bool.false_ne_true b
  · obtain ⟨a, b⟩ := mkA (allN_spec h3 k hk)
    exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩

theorem lab_le {L D P R : Nat → Nat} {nD n : Nat} (h : tabK L D P R nD n = true) (x : Fin 1408) :
    L x.val ≤ n := by
  obtain ⟨h1, h2, -⟩ := tabK_parts h
  by_cases hL : L x.val = 0
  · omega
  · obtain ⟨hp, hd⟩ := h1 x.val x.isLt hL
    have := (h2 _ hp).2.2
    rwa [hd] at this

theorem blk_of {L D P R : Nat → Nat} {nD n : Nat} (ht : tabK L D P R nD n = true) {A B : Nat}
    {g : Equiv.Perm (Fin 1408)} (hev : ∀ x (hx : x < 1408), pt A (pt B x) = (g ⟨x, hx⟩).val)
    (h : blkK L D R nD A B = true) (x : Fin 1408) (hx : L x.val ≠ 0) :
    L (g x).val ≠ 0 ∧ L (g x).val = L (g (finPt R (L x.val - 1))).val := by
  obtain ⟨h1, -, h3⟩ := tabK_parts ht
  obtain ⟨hp, hd⟩ := h1 x.val x.isLt hx
  have hle := lab_le ht x
  have hR := (h3 (L x.val - 1) (by omega)).1
  have e := allN_spec h (P x.val) hp
  unfold blkPt at e
  rw [strictB_app] at e
  obtain ⟨a, b⟩ := mkA e
  rw [hd] at a b
  have b' : L (pt A (pt B x.val)) = L (pt A (pt B (R (L x.val - 1)))) := Nat.eq_of_beq_eq_true b
  have ex : g ⟨x.val, x.isLt⟩ = g x := rfl
  rw [hev x.val x.isLt, hev _ hR, ex] at b'
  rw [hev x.val x.isLt, ex] at a
  rw [finPt_eq hR]
  refine ⟨fun e0 => ?_, b'⟩
  rw [e0] at a
  exact Bool.false_ne_true a

theorem fix_of {L D P R : Nat → Nat} {nD n : Nat} (ht : tabK L D P R nD n = true) {A B : Nat}
    {g : Equiv.Perm (Fin 1408)} (hev : ∀ x (hx : x < 1408), pt A (pt B x) = (g ⟨x, hx⟩).val) :
    fixK L R n A B = true ↔ ∀ k < n, L (g (finPt R k)).val = k + 1 := by
  obtain ⟨-, -, h3⟩ := tabK_parts ht
  unfold fixK
  rw [PK.allN_iff]
  refine forall₂_congr fun k hk => ?_
  rw [finPt_eq (h3 k hk).1, ← hev _ (h3 k hk).1]
  exact ⟨Nat.eq_of_beq_eq_true, fun e => by rw [e]; exact Nat.beq_refl _⟩

def BlkOK (L R : Nat → Nat) (g : Equiv.Perm (Fin 1408)) : Prop :=
  ∀ x : Fin 1408, L x.val ≠ 0 → L (g x).val ≠ 0 ∧ L (g x).val = L (g (finPt R (L x.val - 1))).val

def CommAt2 (c g : Equiv.Perm (Fin 1408)) : Prop :=
  (g * c) ⟨0, by norm_num⟩ = (c * g) ⟨0, by norm_num⟩ ∧
    (g * c) ⟨1401, by norm_num⟩ = (c * g) ⟨1401, by norm_num⟩

theorem comm2_of_comm {c g : Equiv.Perm (Fin 1408)} (h : g * c = c * g) : CommAt2 c g :=
  ⟨by rw [h], by rw [h]⟩

theorem blk_all (hP : Nat.card ↥P1408 = 177408000) {H : Nat} {c : Equiv.Perm (Fin 1408)}
    (hH : RepC H c) {L D P R L' D' P' R' : Nat → Nat} {nD n nD' : Nat}
    (ht : tabK L D P R nD n = true) (ht' : tabK L' D' P' R' nD' 2 = true)
    (hs : shapeK H L D R nD L' D' R' nD' = true) :
    ∀ g ∈ P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))),
      CommAt2 c g → BlkOK L R g ∧ BlkOK L' R' g := by
  unfold shapeK at hs
  rw [strictB_app] at hs
  refine forall_of_scan2 hP hs fun i hi j hj hF hc => ?_
  have hev : ∀ x (hx : x < 1408), pt (T0 i) (pt (T1 j) x) = ((t0Q i * t1Q j) ⟨x, hx⟩).val :=
    fun x hx => ev_eq hi hj hx
  have e : comm2 1401 (T0 i) (T1 j) H = true := (comm2_iff hH hi hj).2 hc
  rw [e] at hF
  obtain ⟨a, b⟩ := mkA hF
  exact ⟨blk_of ht hev a, blk_of ht' hev b⟩

theorem eq_one_of_fix (hP : Nat.card ↥P1408 = 177408000) {H : Nat} {c : Equiv.Perm (Fin 1408)}
    (hH : RepC H c) {L D P R L' D' P' R' : Nat → Nat} {nD n nD' : Nat}
    (ht : tabK L D P R nD n = true) (ht' : tabK L' D' P' R' nD' 2 = true)
    (hk : kerK H L R n L' R' = true) {g : Equiv.Perm (Fin 1408)}
    (hg : g ∈ P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))))
    (hgc : CommAt2 c g) (hf : ∀ k < n, L (g (finPt R k)).val = k + 1)
    (hf' : ∀ k < 2, L' (g (finPt R' k)).val = k + 1) : g = 1 := by
  classical
  unfold kerK at hk
  rw [strictB_app] at hk
  let F : Nat → Nat → Bool := fun A B =>
    bAnd(comm2 1401 A B H, bAnd(fixK L R n A B, fixK L' R' 2 A B))
  have hc1 : cnt2 672 120 T0 T1 F = 1 := Nat.eq_of_beq_eq_true hk
  rw [cnt2_eq] at hc1
  have hmem : ∀ {u : Equiv.Perm (Fin 1408)},
      u ∈ P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) → CommAt2 c u →
      (∀ k < n, L (u (finPt R k)).val = k + 1) → (∀ k < 2, L' (u (finPt R' k)).val = k + 1) →
      ∃ i < 672, ∃ j < 120, u = t0Q i * t1Q j ∧ (i, j) ∈ cbSet F 672 := by
    intro u hu huc huf huf'
    obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hu
    have hev : ∀ x (hx : x < 1408), pt (T0 i) (pt (T1 j) x) = ((t0Q i * t1Q j) ⟨x, hx⟩).val :=
      fun x hx => ev_eq hi hj hx
    refine ⟨i, hi, j, hj, rfl, ?_⟩
    simp only [cbSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨hi, hj⟩, ?_⟩
    change bAnd(comm2 1401 (T0 i) (T1 j) H,
      bAnd(fixK L R n (T0 i) (T1 j), fixK L' R' 2 (T0 i) (T1 j))) = true
    rw [(comm2_iff hH hi hj).2 huc, (fix_of ht hev).2 huf, (fix_of ht' hev).2 huf']
  obtain ⟨i, hi, j, hj, rfl, hp⟩ := hmem hg hgc hf hf'
  have h1 : (1 : Equiv.Perm (Fin 1408)) ∈
      P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) := one_mem _
  obtain ⟨i0, hi0, j0, hj0, e1, hp0⟩ := hmem h1 (comm2_of_comm (by rw [one_mul, mul_one]))
    (fun k hk => by
      rw [Equiv.Perm.one_apply, finPt_val ((tabK_parts ht).2.2 k hk).1]
      exact ((tabK_parts ht).2.2 k hk).2)
    (fun k hk => by
      rw [Equiv.Perm.one_apply, finPt_val ((tabK_parts ht').2.2 k hk).1]
      exact ((tabK_parts ht').2.2 k hk).2)
  have := Finset.card_le_one.1 (le_of_eq hc1) _ hp _ hp0
  simp only [Prod.mk.injEq] at this
  rw [this.1, this.2, ← e1]

theorem shape_of_checks (hP : Nat.card ↥P1408 = 177408000) {H : Nat} {c : Equiv.Perm (Fin 1408)}
    (hH : RepC H c) {L D P R L' D' P' R' : Nat → Nat} {nD n nD' : Nat}
    (ht : tabK L D P R nD n = true) (ht' : tabK L' D' P' R' nD' 2 = true)
    (hs : shapeK H L D R nD L' D' R' nD' = true) (hk : kerK H L R n L' R' = true)
    {X : Type*} [Group X] (φ : X →* Equiv.Perm (Fin 1408)) (hφ : Function.Injective φ)
    (hX : ∀ g, φ g ∈ P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) ∧
      φ g * c = c * φ g) :
    ∃ f : X →* Z 2 × Sym n, Function.Injective f := by
  have hblk := blk_all hP hH ht ht' hs
  have hb : IsBlocks φ (fun x => L x.val) n (finPt R) :=
    { rep := fun k hk => by
        change L (finPt R k).val = k + 1
        rw [finPt_val ((tabK_parts ht).2.2 k hk).1]
        exact ((tabK_parts ht).2.2 k hk).2
      le := lab_le ht
      map := fun g x hx => (hblk _ (hX g).1 (comm2_of_comm (hX g).2)).1 x hx }
  have hb' : IsBlocks φ (fun x => L' x.val) 2 (finPt R') :=
    { rep := fun k hk => by
        change L' (finPt R' k).val = k + 1
        rw [finPt_val ((tabK_parts ht').2.2 k hk).1]
        exact ((tabK_parts ht').2.2 k hk).2
      le := lab_le ht'
      map := fun g x hx => (hblk _ (hX g).1 (comm2_of_comm (hX g).2)).2 x hx }
  refine injective_of_blocks hb hb' fun g hf hf' => hφ ?_
  rw [map_one]
  exact eq_one_of_fix hP hH ht ht' hk (hX g).1 (comm2_of_comm (hX g).2) hf hf'

noncomputable def stabEmb (c : ↥P1408) :
    ↥(Gx (wordP wordB) ⊓ Gx c) →* Equiv.Perm (Fin 1408) :=
  P1408.subtype.comp (Gx (wordP wordB) ⊓ Gx c).subtype

theorem stabEmb_inj (c : ↥P1408) : Function.Injective (stabEmb c) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem stabEmb_mem (c : ↥P1408) (g : ↥(Gx (wordP wordB) ⊓ Gx c)) :
    stabEmb c g ∈ P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) ∧
      stabEmb c g * (c : Equiv.Perm (Fin 1408)) = c * stabEmb c g := by
  obtain ⟨⟨g, hgP⟩, hg1, hg2⟩ := g
  have e1 : (⟨g, hgP⟩ : ↥P1408) * wordP wordB = wordP wordB * ⟨g, hgP⟩ :=
    Subgroup.mem_centralizer_singleton_iff.1 hg1
  have e2 : (⟨g, hgP⟩ : ↥P1408) * c = c * ⟨g, hgP⟩ := Subgroup.mem_centralizer_singleton_iff.1 hg2
  refine ⟨⟨hgP, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, congrArg Subtype.val e2⟩
  have := congrArg Subtype.val e1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_wordP] at this
  exact this

theorem repC_row_i (i : Fin 6) :
    RepC (WK ((tab4Row i).conj ++ wordB ++ (tab4Row i).conj.reverse))
      ((tab4Row i).rowP wordB : Equiv.Perm (Fin 1408)) := by
  rw [coe_rowP]
  exact repC_rowB (letters_row i).1 (letters_row i).2

theorem tab4_inj2 (hP : Nat.card ↥P1408 = 177408000) :
    ∃ f : ↥(Gx (wordP wordB) ⊓ Gx ((tab4Row 2).rowP wordB)) →* Z 2 × Sym 6,
      Function.Injective f :=
  shape_of_checks hP (repC_row_i 2) ch441693_tB2 ch441693_tS2 ch441693_b2 ch441693_k2 _
    (stabEmb_inj _) (stabEmb_mem _)

theorem tab4_inj4 (hP : Nat.card ↥P1408 = 177408000) :
    ∃ f : ↥(Gx (wordP wordB) ⊓ Gx ((tab4Row 4).rowP wordB)) →* Z 2 × Sym 5,
      Function.Injective f :=
  shape_of_checks hP (repC_row_i 4) ch441693_tB4 ch441693_tS4 ch441693_b4 ch441693_k4 _
    (stabEmb_inj _) (stabEmb_mem _)

theorem tab4_inj5 (hP : Nat.card ↥P1408 = 177408000) :
    ∃ f : ↥(Gx (wordP wordB) ⊓ Gx ((tab4Row 5).rowP wordB)) →* Z 2 × Sym 5,
      Function.Injective f :=
  shape_of_checks hP (repC_row_i 5) ch441693_tB5 ch441693_tS5 ch441693_b5 ch441693_k5 _
    (stabEmb_inj _) (stabEmb_mem _)

end CFSG.KD.HN1408.CbT

end
