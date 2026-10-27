module

public import Certificates.Kernel.LyY.Group
public import Certificates.Kernel.LyY.Pair
public import CFSG.Certificates.Kernel.J2Enum.Products
public import CFSG.Certificates.Kernel.LyY.PairSound
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyY

open Equiv Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.J2Enum CFSG.KC.LyY
open CFSG.Monster.B.Co2 CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover CFSG.KC.Child3
open CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.LyonsSims.Ly1080
open CFSG.Sporadic.Th (wordG)

noncomputable abbrev aY : Perm (Fin 1080) := permOfArr 1080 yS[0]!

noncomputable abbrev bY : Perm (Fin 1080) := permOfArr 1080 yS[1]!

theorem prep_aI : Raw.Orb.PRep 1080 11 (YC.SI 0) aY⁻¹ :=
  (Raw.Orb.prep_PS binds ties.2.2.2.2.2 (j := 0) (by norm_num)).2

theorem prep_bI : Raw.Orb.PRep 1080 11 (YC.SI 1) bY⁻¹ :=
  (Raw.Orb.prep_PS binds ties.2.2.2.2.2 (j := 1) (by norm_num)).2

theorem pFix_iff {wd : List ℤ} (hw : ∀ l ∈ wd, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    pFix wd = true ↔ wordG (pairG aY bY) wd = 1 :=
  wordFix_iff (prep_S (j := 0) (by norm_num)) prep_aI (prep_S (j := 1) (by norm_num)) prep_bI hw

theorem wordG_rep_two (k : ℕ) : wordG (pairG aY bY) (List.replicate k 2) = bY ^ k := by
  have h : pairG aY bY 2 = bY := by
    unfold pairG
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold wordG
  rw [List.map_replicate, h, List.prod_replicate]

theorem letters_rep_two (k : ℕ) :
    ∀ l ∈ List.replicate k (2 : ℤ), l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := fun l hl => by
  rw [List.eq_of_mem_replicate hl]
  norm_num

theorem pair_facts : orderOf aY = 2 ∧ orderOf bY = 12 ∧ RelPair aY bY := by
  have h := k_pair
  simp only [bAnd_iff] at h
  obtain ⟨h11, h12, h6, h4, hR, hW⟩ := h
  have hn := k_negP
  simp only [bAnd_iff] at hn
  have hl11 : ∀ l ∈ ([1, 1] : List ℤ), l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by decide
  have hl1 : ∀ l ∈ ([1] : List ℤ), l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by decide
  have ha2 : aY ^ 2 = 1 := by
    have := (pFix_iff hl11).1 h11
    simpa [wordG, pairG, sq] using this
  have ha1 : aY ≠ 1 := by
    intro e
    have h1 : pFix [1] = true := (pFix_iff hl1).2 (by simp [wordG, pairG, e])
    rw [h1] at hn
    exact absurd hn.2 (by decide)
  have hb12 : bY ^ 12 = 1 := by
    rw [← wordG_rep_two]
    exact (pFix_iff (letters_rep_two 12)).1 h12
  have hb6 : bY ^ 6 ≠ 1 := by
    intro e
    rw [← wordG_rep_two] at e
    rw [(pFix_iff (letters_rep_two 6)).2 e] at h6
    exact absurd h6 (by decide)
  have hb4 : bY ^ 4 ≠ 1 := by
    intro e
    rw [← wordG_rep_two] at e
    rw [(pFix_iff (letters_rep_two 4)).2 e] at h4
    exact absurd h4 (by decide)
  refine ⟨orderOf_eq_prime ha2 ha1, ?_, ?_, ?_⟩
  · refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hb12 fun p hp hd => ?_
    have hp12 : p ≤ 12 := Nat.le_of_dvd (by norm_num) hd
    have key : p = 2 ∨ p = 3 := by
      interval_cases p <;> first
        | exact Or.inl rfl | exact Or.inr rfl | (norm_num at hp; done) | (norm_num at hd)
    rcases key with rfl | rfl
    · exact hb6
    · exact hb4
  · intro w hw
    rw [List.all_eq_true] at hR
    exact (pFix_iff (lettersAut.1 w hw)).1 (hR w hw)
  · intro w hw e
    rw [List.all_eq_true] at hW
    have := hW w hw
    rw [(pFix_iff (lettersAut.2 w hw)).2 e] at this
    exact absurd this (by decide)

theorem closure_ab : closure ({aY, bY} : Set (Perm (Fin 1080))) = GY := by
  unfold GY Raw.Orb.Gen
  congr 1
  ext z
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨⟨j, hj⟩, rfl⟩
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl

noncomputable def nFix (σ : Perm (Fin 1080)) : ℕ := (Finset.univ.filter fun p => σ p = p).card

theorem sumF_range (f : ℕ → ℕ) : ∀ m, sumF m f = ∑ i ∈ Finset.range m, f i
  | 0 => rfl
  | m + 1 => by
    change strictN (sumF m f) (fun s' => Nat.add s' (f m)) = _
    rw [strictN_eq', Finset.sum_range_succ, ← sumF_range f m]
    rfl

theorem fixCnt_eq {X : ℕ} {σ : Perm (Fin 1080)} (h : Raw.Orb.PRep 1080 11 X σ) :
    fixCnt 1080 (fun p => pg 11 (mask 11) X p) = nFix σ := by
  unfold fixCnt nFix
  rw [sumF_range, Finset.card_filter, Finset.sum_range]
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  rw [h p, Raw.Orb.beq_dec]
  by_cases e : ((σ p : Fin 1080) : ℕ) = p
  · rw [decide_eq_true e, if_pos (Fin.ext e)]
  · rw [decide_eq_false e, if_neg fun h' => e (congrArg Fin.val h')]

theorem nFix_conj (γ σ : Perm (Fin 1080)) : nFix (γ * σ * γ⁻¹) = nFix σ := by
  unfold nFix
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact (Fintype.card_congr (γ.subtypeEquiv fun p => by simp [Perm.mul_apply])).symm

theorem nFix_one : nFix 1 = 1080 := by
  simp [nFix]

theorem strictB_eqY (y : ℕ) (k : ℕ → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem xo_mem : ∃ ξ ∈ GY, Raw.Orb.PRep 1080 11 xoP ξ := by
  have h := k_fix
  simp only [bAnd_iff] at h
  have hc : Nat.blt XO (rcnt (YC.LR 0) * (rcnt (YC.LR 1) * rcnt (YC.LR 2))) = true := h.1
  rw [ties.2.2.1, ties.2.2.2.1, ties.2.2.2.2.1, Nat.blt_eq] at hc
  have e : xoP = pcomp 1080 11 (mask 11) (YC.TR (roff 1080 (1080 * 11) (YC.LR 0) +
      XO % rcnt (YC.LR 0))) (pcomp 1080 11 (mask 11) (YC.TR (roff 1080 (1080 * 11) (YC.LR 1) +
        XO / rcnt (YC.LR 0) % rcnt (YC.LR 1))) (YC.TR (roff 1080 (1080 * 11) (YC.LR 2) +
          XO / rcnt (YC.LR 0) / rcnt (YC.LR 1)))) := by
    unfold xoP codeProd
    simp only [strictN_eq']
    rfl
  have G := (GrpPf.group3 binds YC.head YC.hl (by norm_num) YC.hs).2.1
  obtain ⟨-, γ0, h0, p0⟩ := G 0 (by norm_num) (XO % rcnt (YC.LR 0)) (by
    rw [ties.2.2.1]; omega)
  obtain ⟨-, γ1, h1, p1⟩ := G 1 (by norm_num) (XO / rcnt (YC.LR 0) % rcnt (YC.LR 1)) (by
    rw [ties.2.2.1, ties.2.2.2.1]; omega)
  obtain ⟨-, γ2, h2, p2⟩ := G 2 (by norm_num) (XO / rcnt (YC.LR 0) / rcnt (YC.LR 1)) (by
    rw [ties.2.2.1, ties.2.2.2.1, ties.2.2.2.2.1]; omega)
  refine ⟨γ0 * (γ1 * γ2), mul_mem h0 (mul_mem h1 h2), ?_⟩
  rw [e]
  exact Raw.Orb.prep_pcomp (by norm_num) p0 (Raw.Orb.prep_pcomp (by norm_num) p1 p2)

theorem fix_bools : allN 1080 (fun p => Nat.beq (pg 11 (mask 11) xoP (pg 11 (mask 11) xoP p)) p) =
      true ∧ Nat.beq (fixCnt 1080 (fun p => pg 11 (mask 11) xoP p)) 120 = true ∧
    Nat.beq (fixCnt 1080 (fun p => pg 11 (mask 11) (YC.S 0) p)) 40 = true := by
  have h := k_fix
  simp only [bAnd_iff] at h
  have h2 := h.2
  rw [strictB_eqY] at h2
  simp only [bAnd_iff] at h2
  exact h2

theorem fix_inv {ξ : Perm (Fin 1080)} (hξ : Raw.Orb.PRep 1080 11 xoP ξ) : ξ ^ 2 = 1 := by
  refine Equiv.ext fun p => Fin.ext ?_
  have := Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 fix_bools.1 p p.2)
  rw [hξ p, hξ (ξ p)] at this
  rw [sq, Perm.mul_apply]
  exact this

theorem fix_120 {ξ : Perm (Fin 1080)} (hξ : Raw.Orb.PRep 1080 11 xoP ξ) : nFix ξ = 120 := by
  rw [← fixCnt_eq hξ]
  exact Nat.eq_of_beq_eq_true fix_bools.2.1

theorem fix_40 : nFix aY = 40 := by
  rw [← fixCnt_eq (prep_S (j := 0) (by norm_num))]
  exact Nat.eq_of_beq_eq_true fix_bools.2.2

theorem fix_facts {ξ : Perm (Fin 1080)} (hξ : Raw.Orb.PRep 1080 11 xoP ξ) :
    orderOf ξ = 2 ∧ nFix ξ = 120 ∧ nFix aY = 40 := by
  refine ⟨orderOf_eq_prime (fix_inv hξ) fun e => ?_, fix_120 hξ, fix_40⟩
  have e120 := fix_120 hξ
  rw [e, nFix_one] at e120
  exact absurd e120 (by norm_num)

theorem card_list {l : List (Perm (Fin 1080))} (h : l.Nodup) : Nat.card {x // x ∈ l} = l.length := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := l) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup h]

theorem conj_mem_order {γ x : Perm (Fin 1080)} (hγ : γ ∈ GY) (hx : x ∈ GY) (ho : orderOf x = 2) :
    γ * x * γ⁻¹ ∈ GY ∧ orderOf (γ * x * γ⁻¹) = 2 :=
  ⟨mul_mem (mul_mem hγ hx) (inv_mem hγ), (MulEquiv.orderOf_eq (MulAut.conj γ) x).trans ho⟩

theorem isConj_hom {G H : Type*} [Group G] [Group H] (f : G →* H) {x z : G} (h : IsConj x z) :
    IsConj (f x) (f z) := by
  rw [isConj_iff] at h ⊢
  obtain ⟨c, rfl⟩ := h
  exact ⟨f c, by simp only [map_mul, map_inv]⟩

theorem isConj_sub {x z : GY} : IsConj x z ↔ ∃ γ ∈ GY, (z : Perm (Fin 1080)) = γ * x * γ⁻¹ := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, rfl⟩
  · rintro ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, Subtype.ext e.symm⟩

theorem card_mulAut_Y0_le : Nat.card (MulAut ↥Y0) ≤ 699840 := by
  classical
  rw [Y0_eq]
  obtain ⟨L, hLnd, hLmem, hF⟩ := CFSG.KC.J2Enum.CntPf.chain_products chainYC
  have hF' : ∀ m, 0 < m → List.Forall₂ (CFSG.Sporadic.Th.Rep 1080)
      (filterProducts 1080 (ordTest 1080 m) (chainTables 1080 yS yBase) (idT 1080) [])
      (L.filter fun x => decide (orderOf x = m)).reverse := fun m hm =>
    hF _ _ fun T x hT => by
      rw [decide_eq_true_iff]
      exact ordTest_iff_perm hT hm
  obtain ⟨hc12, hc2⟩ := counts
  set L2 := (L.filter fun x => decide (orderOf x = 2)).reverse with hL2
  have hL2len : L2.length = 2511 := (hF' 2 (by norm_num)).length_eq.symm.trans hc2
  have hL2mem : ∀ x, x ∈ L2 ↔ x ∈ GY ∧ orderOf x = 2 := fun x => by
    rw [hL2, List.mem_reverse, List.mem_filter, hLmem, decide_eq_true_iff]
  obtain ⟨oa, ob, -⟩ := pair_facts
  obtain ⟨ξ, hξG, hξ⟩ := xo_mem
  obtain ⟨oξ, fξ, fa⟩ := fix_facts hξ
  obtain ⟨La, hLand, hLalen, hLa⟩ :=
    clsOK_sound chainYC (prep_S (j := 0) (by norm_num)) k_ca
  have hco := k_co
  rw [strictB_eqY] at hco
  obtain ⟨Lo, hLond, hLolen, hLo⟩ := clsOK_sound chainYC hξ hco
  have hLaI : ∀ z ∈ La, z ∈ GY ∧ orderOf z = 2 ∧ nFix z = 40 := fun z hz => by
    obtain ⟨γ, hγ, rfl⟩ := hLa z hz
    exact ⟨(conj_mem_order hγ (S_mem (j := 0) (by norm_num)) oa).1,
      (conj_mem_order hγ (S_mem (j := 0) (by norm_num)) oa).2, (nFix_conj γ aY).trans fa⟩
  have hLoI : ∀ z ∈ Lo, z ∈ GY ∧ orderOf z = 2 ∧ nFix z = 120 := fun z hz => by
    obtain ⟨γ, hγ, rfl⟩ := hLo z hz
    exact ⟨(conj_mem_order hγ hξG oξ).1, (conj_mem_order hγ hξG oξ).2,
      (nFix_conj γ ξ).trans fξ⟩
  have hall : ∀ x ∈ GY, orderOf x = 2 → x ∈ La ∨ x ∈ Lo := by
    have hnd : (La ++ Lo).Nodup := List.Nodup.append hLand hLond fun z h1 h2 => by
      have := (hLaI z h1).2.2
      rw [(hLoI z h2).2.2] at this
      exact absurd this (by norm_num)
    have hsub : (La ++ Lo).Subperm L2 := hnd.subperm fun z hz => by
      rw [hL2mem]
      rcases List.mem_append.1 hz with hz | hz
      · exact ⟨(hLaI z hz).1, (hLaI z hz).2.1⟩
      · exact ⟨(hLoI z hz).1, (hLoI z hz).2.1⟩
    have hperm := hsub.perm_of_length_le (by rw [hL2len, List.length_append, hLalen, hLolen])
    intro x hx ho
    exact List.mem_append.1 (hperm.symm.subset ((hL2mem x).2 ⟨hx, ho⟩))
  let o : GY := ⟨ξ, hξG⟩
  have hco81 : Nat.card {z : GY // IsConj o z} ≤ 81 := by
    rw [← hLolen, ← card_list hLond]
    refine Nat.card_le_card_of_injective (fun z => ⟨(z.1 : Perm (Fin 1080)), ?_⟩) fun z z' e => ?_
    · obtain ⟨γ, hγ, e⟩ := isConj_sub.1 z.2
      have hm := conj_mem_order hγ hξG oξ
      rw [← e] at hm
      rcases hall _ hm.1 hm.2 with h | h
      · have h1 := (hLaI _ h).2.2
        rw [e, nFix_conj, fξ] at h1
        exact absurd h1 (by norm_num)
      · exact h
    · have e' := congrArg Subtype.val e
      exact Subtype.ext (Subtype.ext e')
  let P : GY → GY → Prop := fun x y =>
    (orderOf x = 2 ∧ 2430 ≤ Nat.card {z : GY // IsConj x z}) ∧ orderOf y = 12 ∧ RelPair x y
  have hPinv : ∀ (α : MulAut GY) (x y : GY), P x y → P (α x) (α y) := by
    rintro α x y ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨(MulEquiv.orderOf_eq α x).trans h1, ?_⟩, (MulEquiv.orderOf_eq α y).trans h3,
      (relPair_mulEquiv_iff α).2 h4⟩
    refine h2.trans (Nat.card_congr (α.toEquiv.subtypeEquiv fun z => ?_)).le
    constructor
    · exact isConj_hom α.toMonoidHom
    · intro h
      have := isConj_hom α.symm.toMonoidHom h
      simpa using this
  have hsubA : ∀ x y : GY, P x y → (x : Perm (Fin 1080)) ∈ La := by
    rintro x y ⟨⟨h1, h2⟩, -, -⟩
    rw [← Subgroup.orderOf_coe] at h1
    rcases hall _ x.2 h1 with h | h
    · exact h
    · exfalso
      obtain ⟨γ, hγ, e⟩ := hLo _ h
      have hox : IsConj o x := isConj_sub.2 ⟨γ, hγ, e⟩
      have : Nat.card {z : GY // IsConj x z} = Nat.card {z : GY // IsConj o z} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun z =>
          ⟨fun h' => hox.trans h', fun h' => hox.symm.trans h'⟩)
      omega
  let a : GY := ⟨aY, S_mem (j := 0) (by norm_num)⟩
  let b : GY := ⟨bY, S_mem (j := 1) (by norm_num)⟩
  have hgen : closure ({a, b} : Set GY) = ⊤ :=
    closure_pair_subtype_eq_top GY aY bY closure_ab _ _
  have hPab : P a b := by
    refine ⟨⟨(Subgroup.orderOf_coe a).symm.trans oa, ?_⟩, (Subgroup.orderOf_coe b).symm.trans ob,
      (relPair_map_iff (f := GY.subtype) GY.subtype_injective (x := a) (y := b)).1
        pair_facts.2.2⟩
    rw [← hLalen, ← card_list hLand]
    refine Nat.card_le_card_of_injective (fun z => ⟨⟨z.1, (hLaI _ z.2).1⟩, ?_⟩) fun z z' e => ?_
    · obtain ⟨γ, hγ, e⟩ := hLa _ z.2
      exact isConj_sub.2 ⟨γ, hγ, e⟩
    · exact Subtype.ext (congrArg (fun w : {z : GY // IsConj a z} => ((w.1 : GY) :
        Perm (Fin 1080))) e)
  obtain ⟨pc, hpc⟩ : ∃ pc : Perm (Fin 1080) → ℕ, ∀ x, pc x =
      (L.filter fun g => decide (orderOf g = 12)).countP fun y => decide (RelPair x y) :=
    ⟨_, fun _ => rfl⟩
  have hpcard : ∀ x, pc x = Nat.card {y : GY // orderOf (y : Perm (Fin 1080)) = 12 ∧
      RelPair x (y : Perm (Fin 1080))} := by
    intro x
    rw [hpc, List.countP_filter,
      CFSG.Sporadic.Schreier.card_subtype_eq_countP GY L hLnd hLmem
        (fun y => orderOf y = 12 ∧ RelPair x y)]
    congr 1
    funext y
    rw [Bool.decide_and, Bool.and_comm]
  have hpconj : ∀ c ∈ GY, ∀ x, pc (c * x * c⁻¹) = pc x := by
    intro c hc x
    rw [hpcard, hpcard]
    let e : GY ≃ GY := (MulAut.conj (⟨c, hc⟩ : GY)).toEquiv
    refine (Nat.card_congr (e.subtypeEquiv fun y => ?_)).symm
    have he : ((e y : GY) : Perm (Fin 1080)) = c * y * c⁻¹ := rfl
    simp only [he]
    have hoc : orderOf (c * (y : Perm (Fin 1080)) * c⁻¹) = orderOf (y : Perm (Fin 1080)) :=
      MulEquiv.orderOf_eq (MulAut.conj c) (y : Perm (Fin 1080))
    rw [hoc]
    exact and_congr Iff.rfl (relPair_mulEquiv_iff (MulAut.conj c)).symm
  have hpa : pc aY = 288 := by
    rw [hpc, ← (List.reverse_perm _).countP_eq, ← hc12]
    refine (CFSG.Sporadic.Schreier.countP_eq_of_forall₂ (hF' 12 (by norm_num))
      fun T y hT _ => ?_).symm
    rw [decide_eq_true_iff]
    exact relTest_iff (CFSG.KC.J2Enum.CntPf.rep_tabP_of_prep (by norm_num)
      (prep_S (j := 0) (by norm_num))) hT
  have hLaL : (L.filter fun g => decide (g ∈ La)).Perm La := by
    refine (List.perm_ext_iff_of_nodup (hLnd.filter _) hLand).2 fun z => ?_
    rw [List.mem_filter, decide_eq_true_iff, hLmem]
    exact ⟨fun h => h.2, fun h => ⟨(hLaI z h).1, h⟩⟩
  calc Nat.card (MulAut GY)
      ≤ Nat.card {p : GY × GY // P p.1 p.2} := card_mulAut_le_card_pairs a b hgen P hPinv hPab
    _ ≤ Nat.card {p : GY × GY // (p.1 : Perm (Fin 1080)) ∈ La ∧
          orderOf (p.2 : Perm (Fin 1080)) = 12 ∧
          RelPair (p.1 : Perm (Fin 1080)) (p.2 : Perm (Fin 1080))} := by
        refine Nat.card_le_card_of_injective (fun p => ⟨p.1, hsubA _ _ p.2, ?_, ?_⟩)
          fun p q e => Subtype.ext (by have e' := congrArg Subtype.val e; exact e')
        · rw [Subgroup.orderOf_coe]
          exact p.2.2.1
        · exact (relPair_map_iff (f := GY.subtype) GY.subtype_injective).2 p.2.2.2
    _ = ((L.filter fun g => decide (g ∈ La)).map fun x =>
          (L.filter fun g => decide (orderOf g = 12)).countP fun y => decide (RelPair x y)).sum :=
        CFSG.Sporadic.Schreier.card_pairs_eq_sum GY L hLnd hLmem (fun g => g ∈ La)
          (fun g => orderOf g = 12) RelPair
    _ = ((L.filter fun g => decide (g ∈ La)).map fun _ => 288).sum := by
        congr 1
        refine List.map_congr_left fun x hx => ?_
        rw [List.mem_filter, decide_eq_true_iff] at hx
        obtain ⟨γ, hγ, rfl⟩ := hLa x hx.2
        rw [← hpc, hpconj γ hγ, hpa]
    _ = 699840 := by
        rw [List.map_const', List.sum_replicate, smul_eq_mul, hLaL.length_eq, hLalen]

end CertificateChecks.KernelLyY

end
