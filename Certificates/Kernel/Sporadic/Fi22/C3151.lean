
module

public import Certificates.Kernel.Sporadic.Fi22.C3151Base

public import Certificates.Kernel.Sporadic.Fi22.C3151A

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C3151

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Text
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22F2
open CertificateChecks.KernelSpor.Fi22LabA (unpack_get' strictB_eq' offs_parts out6_eq rep_facts
  countP_range_rec)
open CertificateChecks.KernelSpor.Fi22LabX (fixK)

theorem agr_iff {g : Array Nat} {x : Nat × Nat × Nat}
    (hx : CS3.InR fi22TLevels x) : CS3.Agr 3510 fi22TLevels g x ↔ Rep 3510 g (fi22TProd (toF x)) := by
  have e := toF_val hx
  simp only [Prod.ext_iff] at e
  obtain ⟨e1, e2, e3⟩ := e
  constructor
  · intro h p
    rw [h p p.2, fi22TProd_apply, e1, e2, e3]
  · intro h p hp
    rw [h.apply hp, fi22TProd_apply, e1, e2, e3]

theorem rep_prod3 {x : Nat × Nat × Nat}
    (hx : CS3.InR fi22TLevels x) : Rep 3510 (prod3 3510 fi22TLevels x.1 x.2.1 x.2.2) (fi22TProd (toF x)) :=
  (agr_iff hx).1 fun p hp => CS3.prod3_get hp

theorem rep_gT {k : Nat} (hk : k < 9) :
    Rep 3510 ((fi22OuterStrong3510 4).extract 0 9)[k]! (gT k) := by
  rw [gens_get hk]
  exact rep_fi22OuterTStrong (by omega)

theorem rep_gTi {k : Nat} (hk : k < 9) :
    Rep 3510 (((fi22OuterStrong3510 4).extract 0 9).map (invCand 3510))[k]! (gT k)⁻¹ := by
  rw [ginv_get hk]
  exact rep_invCand (rep_fi22OuterTStrong (by omega))

theorem rep_conjA {x : Nat × Nat × Nat} (hx : CS3.InR fi22TLevels x)
    {k : Nat} (hk : k < 9) :
    Rep 3510 (CS3.conjA 3510 fi22TLevels ((fi22OuterStrong3510 4).extract 0 9) k x)
      (gT k * fi22TProd (toF x) * (gT k)⁻¹) := by
  unfold CS3.conjA
  rw [mul_assoc]
  exact rep_compA (rep_gT hk) (rep_compA (rep_prod3 hx) (rep_gTi hk))

theorem exists_agr {g : Array Nat} {G : Equiv.Perm (Fin 3510)}
    (hg : Rep 3510 g G) (hG : G ∈ fi22OuterT) :
    ∃ y, CS3.InR fi22TLevels y ∧ CS3.Agr 3510 fi22TLevels g y := by
  obtain ⟨z, rfl⟩ := fi22TProd_surj hG
  refine ⟨(z.1.val, z.2.1.val, z.2.2.val), by rw [inR_iff]; exact ⟨z.1.2, z.2.1.2, z.2.2.2⟩,
    fun p hp => ?_⟩
  rw [hg.apply hp, fi22TProd_apply]

theorem rep_u {j : Nat} (hj : j < 54) :
    Rep 3510 (fi22OuterStrong3510 7)[j]! (fi22TProd (xF (RT j))) := by
  obtain ⟨hl, -, hp⟩ := root_parts hj
  intro p
  rw [u_eq hj, unpack_get' p.2, hp p p.2, gI_eq hl]

theorem agr_u {j : Nat} (hj : j < 54) :
    CS3.Agr 3510 fi22TLevels (fi22OuterStrong3510 7)[j]! (xN (RT j)) := by
  have hl := (root_parts hj).1
  have hx : CS3.InR fi22TLevels (xN (RT j)) := by
    rw [inR_iff]
    unfold xN
    simp only
    omega
  rw [agr_iff hx, toF_xN hl]
  exact rep_u hj

theorem hyp : CS3.Hyp 3510 fi22TLevels #[0, 1, 2, 3, 6, 4]
    ((fi22OuterStrong3510 4).extract 0 9) (fi22OuterStrong3510 7) where
  pos := by rw [inR_iff]; norm_num
  tr0 := fun p hp => by
    have e := fi22TProd_apply (0, 0, 0) ⟨p, hp⟩
    rw [fi22TProd_zero] at e
    simpa using e.symm
  trlt := fun x hx p hp => by
    have e := fi22TProd_apply (toF x) ⟨p, hp⟩
    have e' := toF_val hx
    simp only [Prod.ext_iff] at e'
    rw [e'.1, e'.2.1, e'.2.2] at e
    rw [← e]
    exact Fin.isLt _
  coord := fun g x hx ha => CS3.coords3_of_agr lvOK (by rw [lev_size]; norm_num) hx ha
  us := fun j hj => by
    rw [size7] at hj
    refine ⟨xN (RT j), ?_, agr_u hj⟩
    rw [inR_iff]
    have := (root_parts hj).1
    unfold xN
    simp only
    omega
  conj := fun x hx k hk => by
    have hk' : k < 9 := by simpa [size4] using hk
    exact exists_agr (rep_conjA hx hk') (Subgroup.mul_mem _ (Subgroup.mul_mem _ (gT_mem hk')
      (fi22TProd_mem _)) (Subgroup.inv_mem _ (gT_mem hk')))
  mul := fun t ht k hk => by
    have hk' : k < 9 := by simpa [size4] using hk
    exact exists_agr (rep_compA (rep_gT hk') (rep_prod3 ht))
      (Subgroup.mul_mem _ (gT_mem hk') (fi22TProd_mem _))
  invlt := fun k hk p hp => by
    have hk' : k < 9 := by simpa [size4] using hk
    exact (rep_gTi hk').lt hp
  inv := fun k hk p hp => by
    have hk' : k < 9 := by simpa [size4] using hk
    have hlt := (rep_gT hk').lt hp
    have e : (⟨(((fi22OuterStrong3510 4).extract 0 9)[k]!)[p]!, hlt⟩ : Fin 3510) =
        gT k ⟨p, hp⟩ := Fin.ext ((rep_gT hk').apply hp)
    rw [(rep_gTi hk').apply hlt, e, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

theorem conj_rep
    {s I J : Nat} (hs : s < 9) (hI : I < 131072) (hJ : J < 131072) (hb : conjB s I J = true) :
    gT s * fi22TProd (xF J) * (gT s)⁻¹ = fi22TProd (xF I) := by
  have hS : Orb.PRep 3510 12 (Fi22TC.S s) (gT s) ∧ Orb.PRep 3510 12 (Fi22TC.SI s) (gT s)⁻¹ :=
    Orb.prep_PS Fi22X.bindsT Fi22X.permT (j := s) (by omega)
  have eS : Fi22TC.S s = Fi22X.TS s := Nat.eq_of_beq_eq_true (allN_spec Fi22X.sOKT s (by omega))
  have key : ∀ t (ht : t < 6), (gT s * fi22TProd (xF J) * (gT s)⁻¹) ⟨bT t, bT_lt ht⟩ =
      fi22TProd (xF I) ⟨bT t, bT_lt ht⟩ := fun t ht => by
    apply Fin.ext
    have hbt := Nat.eq_of_beq_eq_true (allN_spec hb t ht)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have hq : (((gT s)⁻¹ ⟨bT t, bT_lt ht⟩ : Fin 3510) : Nat) =
        pg 12 (mask 12) (Fi22TC.SI s) (bT t) := (hS.2 _).symm
    have h2 : (fi22TProd (xF J) ((gT s)⁻¹ ⟨bT t, bT_lt ht⟩) : Nat) =
        gI J (pg 12 (mask 12) (Fi22TC.SI s) (bT t)) := by
      rw [← gI_eq hJ, hq]
    rw [← hS.1, eS, h2, ← hbt, gI_eq' hI (bT_lt ht)]
  have h1 : (fi22TProd (xF I))⁻¹ * (gT s * fi22TProd (xF J) * (gT s)⁻¹) = 1 :=
    sepT' (Subgroup.mul_mem _ (Subgroup.inv_mem _ (fi22TProd_mem _))
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (gT_mem hs) (fi22TProd_mem _))
        (Subgroup.inv_mem _ (gT_mem hs)))) fun t ht => by
      rw [Equiv.Perm.mul_apply, key t ht, ← Equiv.Perm.mul_apply, inv_mul_cancel,
        Equiv.Perm.one_apply]
  exact (inv_mul_eq_one.1 h1).symm

theorem coord_u {j : Nat} (hj : j < 54) :
    coords3 3510 fi22TLevels #[0, 1, 2, 3, 6, 4] (fi22OuterStrong3510 7)[j]! = xN (RT j) :=
  hyp.coord _ _ (inR_xN (root_parts hj).1) (agr_u hj)

theorem coord_conj
    {s I J : Nat} (hs : s < 9) (hI : I < 131072) (hJ : J < 131072) (hb : conjB s I J = true) :
    coords3 3510 fi22TLevels #[0, 1, 2, 3, 6, 4]
      (CS3.conjA 3510 fi22TLevels ((fi22OuterStrong3510 4).extract 0 9) s (xN J)) = xN I := by
  refine hyp.coord _ _ (inR_xN hI) ?_
  rw [agr_iff (inR_xN hI), toF_xN hI]
  have r := rep_conjA (inR_xN hJ) hs
  rwa [toF_xN hJ, conj_rep hs hI hJ hb] at r

theorem seen
    (Sn : Array Bool)
    (hroot : ∀ j < (fi22OuterStrong3510 7).size, Sn[idx3 fi22TLevels
      (coords3 3510 fi22TLevels #[0, 1, 2, 3, 6, 4] (fi22OuterStrong3510 7)[j]!)]! = true)
    (hcl : ∀ i < CS3.sz fi22TLevels, Sn[i]! = true → ∀ k < ((fi22OuterStrong3510 4).extract 0 9).size,
      Sn[idx3 fi22TLevels (coords3 3510 fi22TLevels #[0, 1, 2, 3, 6, 4]
        (CS3.conjA 3510 fi22TLevels ((fi22OuterStrong3510 4).extract 0 9) k
          (CS3.dec fi22TLevels i)))]! = true) :
    ∀ k < 3263, Sn[SV k]! = true := by
  suffices h : ∀ d k, k < 3263 → DE k = d → Sn[SV k]! = true from fun k hk => h _ k hk rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hk hd
    have hT := tree_parts hk
    unfold treeRow at hT
    rw [strictB_eq', strictB_eq'] at hT
    have hl := (sv_parts hk).1
    by_cases h0 : DE k = 0
    · have hb : Nat.beq (DE k) 0 = true := by rw [h0]; rfl
      obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (bIf_true hT hb)
      have hj := blt_t a
      have := hroot (PR k) (by rw [size7]; exact hj)
      rwa [coord_u hj, idx_xN (root_parts hj).1, Nat.eq_of_beq_eq_true b] at this
    · have hb : Nat.beq (DE k) 0 = false := by
        cases e : Nat.beq (DE k) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) h0
      obtain ⟨a, b, c⟩ := by simpa only [bAnd_iff] using bIf_false hT hb
      rw [strictB_eq'] at c
      obtain ⟨c1, c2⟩ := (bAnd_iff _ _).1 c
      have hp := blt_t a
      have hs := blt_t c1
      have ihp := ih (DE (PR k)) (by rw [← hd]; exact blt_t b) (PR k) hp rfl
      have hpl := (sv_parts hp).1
      have := hcl (SV (PR k)) (by rw [sz_eq]; exact hpl) ihp (GN k) (by simp [size4]; omega)
      rwa [dec_eq, coord_conj hs hl hpl c2, idx_xN hl] at this

theorem wit_ok :
    ∀ x : Fin 1024 × Fin 32 × Fin 4, isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true →
      (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).1 < 54 ∧
      (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.1 < 1024 ∧
      (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.1 < 32 ∧
      (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.2 < 4 ∧
      conjOK3 fi22TLevels 3510
        (fi22OuterStrong3510 7)[(fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).1]!
        x.1 x.2.1 x.2.2
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.1
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.1
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.2 = true := by
  obtain ⟨Sn, hval, hroot, hcl⟩ := CS3.conjSearch3_spec hyp
  have hseen := seen Sn hroot hcl
  intro x hx
  have e0 : (x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val = iX x := rfl
  have ew : fi22CoverWit = conjSearch3 3510 fi22TLevels #[0, 1, 2, 3, 6, 4]
      ((fi22OuterStrong3510 4).extract 0 9) (fi22OuterStrong3510 7) := rfl
  rw [e0, ew]
  have hl := iX_lt x
  have hxI : invB (iX x / 128) (iX x / 4 % 32) (iX x % 4) = true := by
    rw [invB_xF hl, xF_iX]
    exact hx
  obtain ⟨hk, hsv⟩ := (scan_parts (scanOK _ hl)).1 hxI
  have hS : Sn[iX x]! = true := by
    rw [← hsv]
    exact hseen _ hk
  obtain ⟨hj, ht, hok⟩ := hval (iX x) (by rw [sz_eq]; exact hl) hS
  have e : xN (iX x) = (x.1.val, x.2.1.val, x.2.2.val) := by rw [← xF_val hl, xF_iX]
  rw [dec_eq, e] at hok
  rw [inR_iff] at ht
  rw [size7] at hj
  exact ⟨hj, ht.1, ht.2.1, ht.2.2, hok⟩

theorem u_inv
    {j : Nat} (hj : j < 54) : orderOf (fi22TProd (xF (RT j))) = 2 := by
  obtain ⟨hl, hp, -⟩ := root_parts hj
  rw [← isInv3_iff, ← invB_xF hl]
  cases e : invB (RT j / 128) (RT j / 4 % 32) (RT j % 4)
  · have := (scan_parts (scanOK _ hl)).2.1 e
    omega
  · rfl

theorem u_facts :
    ∀ j < 54, siftA 3510 fi22TLevels #[0, 1, 2, 3, 6, 4] 0 (fi22OuterStrong3510 7)[j]! = true ∧
      eqA 3510 (fi22OuterStrong3510 7)[j]! (idA 3510) = false ∧
      eqA 3510 (compA 3510 (fi22OuterStrong3510 7)[j]! (fi22OuterStrong3510 7)[j]!)
        (idA 3510) = true ∧
      siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
        (fi22OuterStrong3510 8)[j]! = true ∧
      ∃ i < 3, eqA 3510 (compA 3510 (fi22OuterStrong3510 8)[j]! (fi22OuterStrong3510 7)[j]!)
        (compA 3510 (fi22OuterStrong3510 6)[i]! (fi22OuterStrong3510 8)[j]!) = true := by
  intro j hj
  have ru := rep_u hj
  have ho := u_inv hj
  obtain ⟨h2, hne⟩ := (orderOf_eq_prime_iff.1 ho)
  obtain ⟨cH, sH, cU, i, hi, hc⟩ := h_parts hj
  obtain ⟨h6, -, -, -, -, -, -, -, -, hP, -⟩ := rep_facts
  have cO : Fi22X.cn (Fi22LabX.O6 i) = true := by
    rw [← h6 i hi]
    exact (hP i hi).1
  refine ⟨(siftA_iff_mem_originalSubgroup fi22OuterChainT_arrays (by norm_num)
      fi22Local_check.2.2.1 ru).2 (fi22TProd_mem _), ?_, ?_,
    Fi22C3150.siftA_of (h_eq hj) cH sH, i, hi, ?_⟩
  · cases e : eqA 3510 (fi22OuterStrong3510 7)[j]! (idA 3510)
    · rfl
    · exact absurd ((eqA_iff ru rep_idA).1 e) hne
  · rw [eqA_iff (rep_compA ru ru) rep_idA, ← pow_two]
    exact h2
  · rw [h_eq hj, u_eq hj, out6_eq hi, Fi22X.comp_eq cH cU, Fi22X.comp_eq cO cH]
    exact Fi22X.eqA_of (Fi22X.cn_c cH cU) (Fi22X.cn_c cO cH) hc

theorem facts :
    fi22OuterTPointsNat.Nodup ∧
      (∀ k < 9, ∀ p < 3510, fi22OuterTPointsNat.contains p =
        fi22OuterTPointsNat.contains ((fi22OuterStrong3510 4)[k]!)[p]!) ∧
      (∀ x : Fin 1024 × Fin 32 × Fin 4, x ≠ (0, 0, 0) →
        moves3 fi22TLevels fi22TPointsArr x.1 x.2.1 x.2.2 = true) ∧
      (Finset.univ.filter fun x : Fin 1024 × Fin 32 × Fin 4 =>
        isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true).card = 3263 ∧
      (∀ x : Fin 1024 × Fin 32 × Fin 4, isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true →
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).1 < 54 ∧
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.1 < 1024 ∧
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.1 < 32 ∧
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.2 < 4 ∧
        conjOK3 fi22TLevels 3510
          (fi22OuterStrong3510 7)[(fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).1]!
          x.1 x.2.1 x.2.2
          (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.1
          (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.1
          (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.2 = true) ∧
      (∀ j < 54, siftA 3510 fi22TLevels #[0, 1, 2, 3, 6, 4] 0 (fi22OuterStrong3510 7)[j]! = true ∧
        eqA 3510 (fi22OuterStrong3510 7)[j]! (idA 3510) = false ∧
        eqA 3510 (compA 3510 (fi22OuterStrong3510 7)[j]! (fi22OuterStrong3510 7)[j]!)
          (idA 3510) = true ∧
        siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
          (fi22OuterStrong3510 8)[j]! = true ∧
        ∃ i < 3, eqA 3510 (compA 3510 (fi22OuterStrong3510 8)[j]! (fi22OuterStrong3510 7)[j]!)
          (compA 3510 (fi22OuterStrong3510 6)[i]! (fi22OuterStrong3510 8)[j]!) = true) ∧
      (∀ i < 3, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
          (fi22OuterStrong3510 6)[i]! = true ∧
        eqA 3510 (fi22OuterStrong3510 6)[i]! (idA 3510) = false ∧
        eqA 3510 (compA 3510 (fi22OuterStrong3510 6)[i]! (fi22OuterStrong3510 6)[i]!)
          (idA 3510) = true) ∧
      (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[0]!)[p.val]! = p.val).card =
        54 ∧
      (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[1]!)[p.val]! = p.val).card =
        182 ∧
      (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[2]!)[p.val]! = p.val).card =
        694 ∧
      eqA 3510 (fi22OuterStrong3510 6)[2]! (fi22OuterStrong3510 1)[0]! = true :=
  ⟨tp_nodup, tp_inv, tp_moves, card_inv scanOK, wit_ok, u_facts, x_facts, fix_counts.1,
    fix_counts.2.1, fix_counts.2.2, x3_eq⟩

open CFSG.Monster.B.Fischer CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate3151_of :
 fi22OuterTPointsNat.Nodup ∧
      (∀ k < 9, ∀ p < 3510, fi22OuterTPointsNat.contains p =
        fi22OuterTPointsNat.contains ((fi22OuterStrong3510 4)[k]!)[p]!) ∧
      (∀ x : Fin 1024 × Fin 32 × Fin 4, x ≠ (0, 0, 0) →
        moves3 fi22TLevels fi22TPointsArr x.1 x.2.1 x.2.2 = true) ∧
      (Finset.univ.filter fun x : Fin 1024 × Fin 32 × Fin 4 =>
        isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true).card = 3263 ∧
      (∀ x : Fin 1024 × Fin 32 × Fin 4, isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true →
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).1 < 54 ∧
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.1 < 1024 ∧
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.1 < 32 ∧
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.2 < 4 ∧
        conjOK3 fi22TLevels 3510
          (fi22OuterStrong3510 7)[(fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).1]!
          x.1 x.2.1 x.2.2
          (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.1
          (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.1
          (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.2 = true) ∧
      (∀ j < 54, siftA 3510 fi22TLevels #[0, 1, 2, 3, 6, 4] 0 (fi22OuterStrong3510 7)[j]! = true ∧
        eqA 3510 (fi22OuterStrong3510 7)[j]! (idA 3510) = false ∧
        eqA 3510 (compA 3510 (fi22OuterStrong3510 7)[j]! (fi22OuterStrong3510 7)[j]!)
          (idA 3510) = true ∧
        siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
          (fi22OuterStrong3510 8)[j]! = true ∧
        ∃ i < 3, eqA 3510 (compA 3510 (fi22OuterStrong3510 8)[j]! (fi22OuterStrong3510 7)[j]!)
          (compA 3510 (fi22OuterStrong3510 6)[i]! (fi22OuterStrong3510 8)[j]!) = true) ∧
      (∀ i < 3, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
          (fi22OuterStrong3510 6)[i]! = true ∧
        eqA 3510 (fi22OuterStrong3510 6)[i]! (idA 3510) = false ∧
        eqA 3510 (compA 3510 (fi22OuterStrong3510 6)[i]! (fi22OuterStrong3510 6)[i]!)
          (idA 3510) = true) ∧
      (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[0]!)[p.val]! = p.val).card =
        54 ∧
      (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[1]!)[p.val]! = p.val).card =
        182 ∧
      (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[2]!)[p.val]! = p.val).card =
        694 ∧
      eqA 3510 (fi22OuterStrong3510 6)[2]! (fi22OuterStrong3510 1)[0]! = true :=
  facts

end CertificateChecks.KernelSpor.Fi22C3151

end
