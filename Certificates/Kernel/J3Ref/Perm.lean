module

public import Certificates.Kernel.J3Ref.Faith

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3Ref

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnumB CFSG.KS.MulH
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31.Native

abbrev Pm : Type := Equiv.Perm (Fin 6156)

noncomputable abbrev tab (X : Nat) : Table := tabT (unpack 6156 13 X)

@[expose] def HasP (X : Nat) (A : Pm) : Prop :=
  canonK 6156 13 (mask 13) (6156 * 13) X = true ∧ A ∈ KernelK426J3.GJ ∧
    ∀ x : Fin 6156, pg 13 (mask 13) X x = (A x : Nat)

theorem hasP_of_mj {X : Nat} (h : MJ X) : ∃ A, HasP X A := by
  unfold MJ at h
  obtain ⟨c, A, hA, hp⟩ := h
  exact ⟨A, c, hA, hp⟩

theorem HasP.at {X : Nat} {A : Pm} (h : HasP X A) {y : Nat} (hy : y < 6156) :
    pg 13 (mask 13) X y = (A ⟨y, hy⟩ : Nat) :=
  h.2.2 ⟨y, hy⟩

theorem rep_tab {X : Nat} {A : Pm} (h : HasP X A) : Rep 6156 (tab X) A := by
  intro i hi
  rw [ap_tabT _ (unpack_lt h.1), KernelK426J3.unpackGet hi, idx_of_lt _ hi, h.at hi]
  rfl

theorem bs_lt' {b : Nat} (hb : b ∈ bsJ) : b < 6156 := by
  simp only [bsJ, List.mem_cons, List.not_mem_nil, or_false] at hb
  omega

theorem eq_iff_base {A B : Pm} (hA : A ∈ KernelK426J3.GJ) (hB : B ∈ KernelK426J3.GJ) :
    A = B ↔ ∀ b (hb : b ∈ bsJ), (A ⟨b, bs_lt' hb⟩ : Nat) = B ⟨b, bs_lt' hb⟩ := by
  constructor
  · rintro rfl b hb
    rfl
  · intro h
    exact KernelK426J3.eq_of_base hA hB fun b hb => h b (by simpa [bsJ, KernelK426J3.bs] using hb)

theorem listAll_iff (f : Nat → Bool) (bs : List Nat) :
    List.rec (motive := fun _ => Bool) true
      (fun b _ ih => Bool.rec (motive := fun _ => Bool) false ih (f b)) bs = true ↔
      ∀ b ∈ bs, f b = true := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    change Bool.rec (motive := fun _ => Bool) false _ (f b) = true ↔ _
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem tblEq_eq {S T : Table} {g h : Pm} (hS : Rep 6156 S g) (hT : Rep 6156 T h) :
    tblEq 6156 S T = decide (g = h) := by
  rw [Bool.eq_iff_iff, CFSG.KS.Tbl.tblEq_iff_eq hS hT, decide_eq_true_iff]

theorem sqB_eq {X : Nat} {A : Pm} (h : HasP X A) :
    sqB 13 (mask 13) bsJ X = decide (A * A = 1) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eq_iff_base (KernelK426J3.GJ.mul_mem h.2.1 h.2.1)
    KernelK426J3.GJ.one_mem]
  unfold sqB
  rw [listAll_iff]
  refine forall_congr' fun b => ⟨fun hb hm => ?_, fun hb hm => ?_⟩
  · have e := Nat.eq_of_beq_eq_true (hb hm)
    rw [h.at (bs_lt' hm), h.at (A ⟨b, bs_lt' hm⟩).isLt] at e
    exact e
  · have e := hb hm
    rw [Nat.beq_eq, h.at (bs_lt' hm), h.at (A ⟨b, bs_lt' hm⟩).isLt]
    exact e

theorem commB_eq {X Y : Nat} {A B : Pm} (hX : HasP X A) (hY : HasP Y B) :
    commB 13 (mask 13) bsJ X Y = decide (A * B = B * A) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eq_iff_base (KernelK426J3.GJ.mul_mem hX.2.1 hY.2.1)
    (KernelK426J3.GJ.mul_mem hY.2.1 hX.2.1)]
  unfold commB
  rw [listAll_iff]
  refine forall_congr' fun b => ⟨fun hb hm => ?_, fun hb hm => ?_⟩
  · have e := Nat.eq_of_beq_eq_true (hb hm)
    rw [hY.at (bs_lt' hm), hX.at (B ⟨b, bs_lt' hm⟩).isLt, hX.at (bs_lt' hm),
      hY.at (A ⟨b, bs_lt' hm⟩).isLt] at e
    exact e
  · have e := hb hm
    rw [Nat.beq_eq, hY.at (bs_lt' hm), hX.at (B ⟨b, bs_lt' hm⟩).isLt, hX.at (bs_lt' hm),
      hY.at (A ⟨b, bs_lt' hm⟩).isLt]
    exact e

theorem tblEq_sq {X : Nat} {A : Pm} (h : HasP X A) :
    tblEq 6156 (compT 6156 (tab X) (tab X)) (idT 6156) = sqB 13 (mask 13) bsJ X := by
  rw [sqB_eq h, tblEq_eq ((rep_tab h).compT (rep_tab h)) (Rep.idT (by norm_num))]

theorem commTT_eq {X Y : Nat} {A B : Pm} (hX : HasP X A) (hY : HasP Y B) :
    CFSG.Sporadic.SmallOddCore.commTT 6156 (tab X) (tab Y) = commB 13 (mask 13) bsJ X Y := by
  unfold CFSG.Sporadic.SmallOddCore.commTT
  rw [commB_eq hX hY, tblEq_eq ((rep_tab hX).compT (rep_tab hY)) ((rep_tab hY).compT (rep_tab hX))]

theorem commT_eq {X Y : Nat} {A B : Pm} (hX : HasP X A) (hY : HasP Y B) :
    commT 6156 (tab X) (tab Y) = commB 13 (mask 13) bsJ X Y := by
  unfold commT
  rw [commB_eq hX hY, tblEq_eq ((rep_tab hX).compT (rep_tab hY)) ((rep_tab hY).compT (rep_tab hX))]

@[expose] noncomputable def spanP : List Pm → Nat → Pm
  | [], _ => 1
  | a :: Ls, c => (if c % 2 = 1 then a else 1) * spanP Ls (c / 2)

theorem spanP_mem : ∀ (Ls : List Pm), (∀ a ∈ Ls, a ∈ KernelK426J3.GJ) → ∀ c,
    spanP Ls c ∈ KernelK426J3.GJ
  | [], _, _ => KernelK426J3.GJ.one_mem
  | a :: Ls, h, c => by
    rw [spanP]
    refine KernelK426J3.GJ.mul_mem ?_ (spanP_mem Ls (fun b hb => h b (List.mem_cons_of_mem a hb)) _)
    split_ifs
    · exact h a List.mem_cons_self
    · exact KernelK426J3.GJ.one_mem

theorem spanAtL_eq : ∀ (L : List Nat) (Ls : List Pm), List.Forall₂ HasP L Ls → ∀ c y
    (hy : y < 6156), spanAtL 13 (mask 13) L c y = (spanP Ls c ⟨y, hy⟩ : Nat)
  | [], [], _, _, _, _ => rfl
  | X :: L, A :: Ls, List.Forall₂.cons hXA hL, c, y, hy => by
    have ih := spanAtL_eq L Ls hL (c / 2) y hy
    change nIf(Nat.beq (Nat.mod c 2) 1, pg 13 (mask 13) X (spanAtL 13 (mask 13) L (Nat.div c 2) y),
      spanAtL 13 (mask 13) L (Nat.div c 2) y) = _
    rw [CFSG.KS.Raw.Orb.nIf_eq, spanP, Equiv.Perm.mul_apply]
    have ih' : spanAtL 13 (mask 13) L (Nat.div c 2) y = (spanP Ls (c / 2) ⟨y, hy⟩ : Nat) := ih
    by_cases hm : c % 2 = 1
    · have e : Nat.beq (Nat.mod c 2) 1 = true := by
        rw [Nat.beq_eq]
        exact hm
      rw [if_pos e, if_pos hm, ih', hXA.at (spanP Ls (c / 2) ⟨y, hy⟩).isLt]
    · have e : Nat.beq (Nat.mod c 2) 1 = false := by
        cases e : Nat.beq (Nat.mod c 2) 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hm
      rw [if_neg (by rw [e]; decide), if_neg hm, ih']
      rfl

theorem spanP_mem_of {L : List Nat} {Ls : List Pm} (hL : List.Forall₂ HasP L Ls) (c : Nat) :
    spanP Ls c ∈ KernelK426J3.GJ := by
  refine spanP_mem Ls ?_ c
  induction hL with
  | nil => simp
  | cons hXA _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hXA.2.1
    · exact ih a ha

theorem spanEqB_eq {L : List Nat} {Ls : List Pm} (hL : List.Forall₂ HasP L Ls) {X : Nat} {A : Pm}
    (h : HasP X A) (c : Nat) :
    spanEqB 13 (mask 13) bsJ L X c = decide (A = spanP Ls c) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eq_iff_base h.2.1 (spanP_mem_of hL c)]
  unfold spanEqB
  rw [listAll_iff]
  refine forall_congr' fun b => ⟨fun hb hm => ?_, fun hb hm => ?_⟩
  · have e := Nat.eq_of_beq_eq_true (hb hm)
    rw [h.at (bs_lt' hm), spanAtL_eq L Ls hL c b (bs_lt' hm)] at e
    exact e
  · rw [Nat.beq_eq, h.at (bs_lt' hm), spanAtL_eq L Ls hL c b (bs_lt' hm)]
    exact hb hm

theorem spanCompB_eq {L : List Nat} {Ls : List Pm} (hL : List.Forall₂ HasP L Ls) {X B Y : Nat}
    {A Bp C : Pm} (hX : HasP X A) (hB : HasP B Bp) (hY : HasP Y C) (c : Nat) :
    spanCompB 13 (mask 13) bsJ L X B Y c = decide (A * Bp = spanP Ls c * C) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eq_iff_base (KernelK426J3.GJ.mul_mem hX.2.1 hB.2.1)
    (KernelK426J3.GJ.mul_mem (spanP_mem_of hL c) hY.2.1)]
  unfold spanCompB
  rw [listAll_iff]
  refine forall_congr' fun b => ⟨fun hb hm => ?_, fun hb hm => ?_⟩
  · have e := Nat.eq_of_beq_eq_true (hb hm)
    rw [hB.at (bs_lt' hm), hX.at (Bp ⟨b, bs_lt' hm⟩).isLt, hY.at (bs_lt' hm),
      spanAtL_eq L Ls hL c _ (C ⟨b, bs_lt' hm⟩).isLt] at e
    exact e
  · rw [Nat.beq_eq, hB.at (bs_lt' hm), hX.at (Bp ⟨b, bs_lt' hm⟩).isLt, hY.at (bs_lt' hm),
      spanAtL_eq L Ls hL c _ (C ⟨b, bs_lt' hm⟩).isLt]
    exact hb hm

theorem conjSpanB_eq {L : List Nat} {Ls : List Pm} (hL : List.Forall₂ HasP L Ls) {S X : Nat}
    {Sp A : Pm} (hS : HasP S Sp) (hX : HasP X A) (c : Nat) :
    conjSpanB 13 (mask 13) bsJ L S X c = decide (Sp * spanP Ls c = A * Sp) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eq_iff_base
    (KernelK426J3.GJ.mul_mem hS.2.1 (spanP_mem_of hL c)) (KernelK426J3.GJ.mul_mem hX.2.1 hS.2.1)]
  unfold conjSpanB
  rw [listAll_iff]
  refine forall_congr' fun b => ⟨fun hb hm => ?_, fun hb hm => ?_⟩
  · have e := Nat.eq_of_beq_eq_true (hb hm)
    rw [spanAtL_eq L Ls hL c b (bs_lt' hm), hS.at (spanP Ls c ⟨b, bs_lt' hm⟩).isLt,
      hS.at (bs_lt' hm), hX.at (Sp ⟨b, bs_lt' hm⟩).isLt] at e
    exact e
  · rw [Nat.beq_eq, spanAtL_eq L Ls hL c b (bs_lt' hm), hS.at (spanP Ls c ⟨b, bs_lt' hm⟩).isLt,
      hS.at (bs_lt' hm), hX.at (Sp ⟨b, bs_lt' hm⟩).isLt]
    exact hb hm

theorem anyMaskB_eq (d : Nat) (f : Nat → Bool) :
    anyMaskB d f = (List.range (2 ^ d)).any f := by
  unfold anyMaskB
  rw [Bool.eq_iff_iff, Bool.not_eq_true', List.any_eq_true]
  rw [show Nat.pow 2 d = 2 ^ d from rfl]
  constructor
  · intro h
    by_contra hc
    rw [Bool.eq_false_iff] at h
    exact h (CFSG.KS.Raw.Orb.allN_iff.2 fun c hc' => by
      cases e : f c
      · rfl
      · exact absurd ⟨c, List.mem_range.2 hc', e⟩ hc)
  · rintro ⟨c, hc, hf⟩
    cases e : allN (2 ^ d) (fun c => !(f c))
    · rfl
    · have := CFSG.KS.Raw.Orb.allN_iff.1 e c (List.mem_range.1 hc)
      simp [hf] at this

theorem rep_maskProd : ∀ (L : List Nat) (Ls : List Pm), List.Forall₂ HasP L Ls → ∀ c,
    Rep 6156 (maskProd 6156 (L.map tab) c) (spanP Ls c)
  | [], [], _, _ => Rep.idT (by norm_num)
  | X :: L, A :: Ls, List.Forall₂.cons hXA hL, c => by
    rw [List.map_cons, maskProd, spanP]
    refine Rep.compT ?_ (rep_maskProd L Ls hL (c / 2))
    split_ifs
    · exact rep_tab hXA
    · exact Rep.idT (by norm_num)

end CertificateChecks.KernelJ3Ref

end
