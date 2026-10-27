
module

public import Certificates.Kernel.U43Mod.OutChecks
public import Certificates.Kernel.U43Mod.InvGlue
public import Certificates.Kernel.U43Mod.Glue3962
public import CFSG.Certificates.Kernel.U43Mod.OutSound
public import CFSG.Certificates.Kernel.U43Mod.OutBridge
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Out

open CFSG.KC.Enum CFSG.KC.U43Inv CFSG.KC.U43Out CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.U43Mod
  CFSG.KS.U43Inv CFSG.KS.U43Out CFSG.KS.U43Mod.LieOdd CertificateChecks.KernelU43Inv
  CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out

theorem pg1023 (X q : ℕ) : pg 10 1023 X q = pg 10 (mask 10) X q := rfl

theorem sbEq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := CFSG.KS.U43Mod.strictB_eq y k

theorem blt_false {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff]
  intro e
  exact h (blt_iff.1 e)

theorem prep_d' (q : ℕ) (hq : q < 820) :
    pg 10 1023 (KernelU43Aut3962.DT 0) q = (dPerm ⟨q, hq⟩ : ℕ) ∧
      pg 10 1023 (KernelU43Aut3962.DTI 0) q = (dPerm⁻¹ ⟨q, hq⟩ : ℕ) :=
  ⟨by rw [pg1023]; exact KernelU43Aut3962.prep_d.1 ⟨q, hq⟩,
    by rw [pg1023]; exact KernelU43Aut3962.prep_d.2 ⟨q, hq⟩⟩

theorem prep_s' (q : ℕ) (hq : q < 820) :
    pg 10 1023 (KernelU43Aut3962.DT 1) q = (sPerm ⟨q, hq⟩ : ℕ) ∧
      pg 10 1023 (KernelU43Aut3962.DTI 1) q = (sPerm⁻¹ ⟨q, hq⟩ : ℕ) :=
  ⟨by rw [pg1023]; exact KernelU43Aut3962.prep_s.1 ⟨q, hq⟩,
    by rw [pg1023]; exact KernelU43Aut3962.prep_s.2 ⟨q, hq⟩⟩

theorem LP8_eq (l q : ℕ) (hq : q < 820) : LP8 l q = (letP l ⟨q, hq⟩ : ℕ) := by
  unfold LP8
  by_cases h4 : l < 4
  · rw [blt_iff.2 h4]
    dsimp only
    rw [LP_eq l q hq]
    simp [letP, h4]
  rw [blt_false h4]
  dsimp only
  by_cases e4 : l = 4
  · rw [beq_iff.2 e4]
    dsimp only
    subst e4
    rw [(prep_d' q hq).1]
    simp [letP]
  rw [beq_false e4]
  dsimp only
  by_cases e5 : l = 5
  · rw [beq_iff.2 e5]
    dsimp only
    subst e5
    rw [(prep_s' q hq).1]
    simp [letP]
  rw [beq_false e5]
  dsimp only
  by_cases e6 : l = 6
  · rw [beq_iff.2 e6]
    dsimp only
    subst e6
    rw [(prep_d' q hq).2]
    simp [letP]
  rw [beq_false e6]
  dsimp only
  rw [(prep_s' q hq).2]
  simp [letP, h4, e4, e5, e6]

theorem mwv8_eq (w : List ℕ) (q : ℕ) (hq : q < 820) : mwv LP8 w q = (wordP w ⟨q, hq⟩ : ℕ) :=
  mwvP_eq LP8_eq w q hq

theorem rpt_gen {A B : ℕ} {a b : Gp} (hA : ∀ q (hq : q < 820), pg 10 1023 A q = (a ⟨q, hq⟩ : ℕ))
    (hB : ∀ q (hq : q < 820), pg 10 1023 B q = (b ⟨q, hq⟩ : ℕ)) (j : ℕ) (hj : j < 2) (q : ℕ)
    (hq : q < 820) : ∀ i, rpt A B i j q = ((a ^ i * b ^ j) ⟨q, hq⟩ : ℕ)
  | 0 => by
    interval_cases j
    · simp [rpt]
    · simp only [pow_zero, pow_one, one_mul]
      exact hB q hq
  | i + 1 => by
    have e : rpt A B (i + 1) j q = pg 10 1023 A (rpt A B i j q) := rfl
    rw [e, rpt_gen hA hB j hj q hq i, hA _ (Fin.is_lt _), Fin.eta, pow_succ', mul_assoc]
    simp only [Equiv.Perm.mul_apply]

theorem rpt_eq (j : ℕ) (hj : j < 2) (q : ℕ) (hq : q < 820) (i : ℕ) :
    rpt (KernelU43Aut3962.DT 0) (KernelU43Aut3962.DT 1) i j q = (dsPerm i j ⟨q, hq⟩ : ℕ) :=
  rpt_gen (fun q hq => (prep_d' q hq).1) (fun q hq => (prep_s' q hq).1) j hj q hq i

theorem sRec_spec {i j : ℕ} (hi : i < 4) (hj : j < 2) :
    base3 (pwv LP (MW (2 * i + j)) (ML (2 * i + j)))
        (rpt (KernelU43Aut3962.DT 0) (KernelU43Aut3962.DT 1) i j) = true ∧
      (2 * i + j ≠ 0 → pwv LP (MW (2 * i + j)) (ML (2 * i + j)) 84 ≠
        rpt (KernelU43Aut3962.DT 0) (KernelU43Aut3962.DT 1) i j 84) := by
  have h := allN_spec kSep (2 * i + j) (by omega)
  have e1 : Nat.shiftRight (2 * i + j) 1 = i := by
    change (2 * i + j) >>> 1 = i
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e2 : Nat.land (2 * i + j) 1 = j := by
    change (2 * i + j) &&& 1 = j
    rw [Nat.and_one_is_mod]
    omega
  unfold sRec at h
  rw [U43Mod.strictB_eq, U43Mod.strictB_eq, e1, e2, bAnd_iff] at h
  refine ⟨h.1, fun hc => ?_⟩
  have h2 := h.2
  rw [beq_false hc] at h2
  dsimp only at h2
  exact beq_false_iff.1 (bNot_iff.1 h2)

theorem coset_cover {g : Gp} (hg : g ∈ Nrm) :
    ∃ i < 4, ∃ j < 2, ∃ n ∈ Nsub, g = n * dsPerm i j := by
  have hf := autFacts
  let N' := Nsub.subgroupOf Nrm
  let f : Fin 4 × Fin 2 → Nrm ⧸ N' := fun ij =>
    ((⟨dsPerm ij.1 ij.2, dsPerm_mem hf _ _⟩ : Nrm) : Nrm ⧸ N')
  have hinj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    have h' := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h'
    have h'' : (dsPerm i j)⁻¹ * dsPerm k l ∈ Nsub := by simpa using h'
    obtain ⟨e1, e2⟩ := KernelU43Aut3962.cos_eq i.2 j.2 k.2 l.2 h''
    ext
    · exact e1
    · exact e2
  have hcard : Nat.card (Nrm ⧸ N') = 8 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
    have h2 : Nat.card N' = Nat.card Nsub :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Nsub_le_Nrm).toEquiv
    rw [h2, card_Nsub, card_Nrm] at h1
    omega
  have hfin : Finite (Nrm ⧸ N') := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard]; simp)
  obtain ⟨⟨i, j⟩, hij⟩ := hbij.2 ((⟨g, hg⟩ : Nrm) : Nrm ⧸ N')
  have h' := QuotientGroup.eq.1 hij
  rw [Subgroup.mem_subgroupOf] at h'
  have hn : (dsPerm i j)⁻¹ * g ∈ Nsub := by simpa using h'
  refine ⟨i, i.2, j, j.2, dsPerm i j * ((dsPerm i j)⁻¹ * g) * (dsPerm i j)⁻¹,
    conj_mem_Nsub (dsPerm_mem hf _ _) hn, by group⟩

theorem fix_one {g : Gp} (hg : g ∈ Nrm)
    (h0 : g ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩) (h1 : g ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩)
    (h9 : g ⟨9, by norm_num⟩ = ⟨9, by norm_num⟩) (h84 : g ⟨84, by norm_num⟩ = ⟨84, by norm_num⟩) :
    g = 1 := by
  obtain ⟨i, hi, j, hj, n, ⟨y, rfl⟩, rfl⟩ := coset_cover hg
  obtain ⟨hb, h84'⟩ := sRec_spec hi hj
  obtain ⟨x, hx⟩ := pwv_mem (fun l _ q hq => LP_eq l q hq) (MW (2 * i + j)) (ML (2 * i + j))
  obtain ⟨b0, b1, b9⟩ := base3_spec hb
  rw [hx 0 (by norm_num), rpt_eq j hj 0 (by norm_num)] at b0
  rw [hx 1 (by norm_num), rpt_eq j hj 1 (by norm_num)] at b1
  rw [hx 9 (by norm_num), rpt_eq j hj 9 (by norm_num)] at b9
  have hyx : y * x = 1 := by
    refine hsep _ _ ?_ ?_ ?_
    · rw [map_mul, map_one, Equiv.Perm.mul_apply, Fin.ext_iff.2 b0]
      exact congrArg Fin.val h0
    · rw [map_mul, map_one, Equiv.Perm.mul_apply, Fin.ext_iff.2 b1]
      exact congrArg Fin.val h1
    · rw [map_mul, map_one, Equiv.Perm.mul_apply, Fin.ext_iff.2 b9]
      exact congrArg Fin.val h9
  have hy : psi y = (psi x)⁻¹ := by
    rw [← map_inv, eq_inv_of_mul_eq_one_left hyx]
  by_cases hc : 2 * i + j = 0
  · have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0 hj0
    have hx1 : x = 1 := by
      refine hsep _ _ ?_ ?_ ?_
      · rw [b0]
        simp [dsPerm]
      · rw [b1]
        simp [dsPerm]
      · rw [b9]
        simp [dsPerm]
    rw [hy, hx1]
    simp [dsPerm]
  · exfalso
    apply h84' hc
    rw [hx 84 (by norm_num), rpt_eq j hj 84 (by norm_num)]
    have e := congrArg (fun z => (psi x z : ℕ)) h84
    simp only [hy, Equiv.Perm.mul_apply] at e
    rw [← Equiv.Perm.mul_apply (psi x), mul_inv_cancel, Equiv.Perm.one_apply] at e
    exact e.symm

theorem sep4 {g h : Gp} (hg : g ∈ Nrm) (hh : h ∈ Nrm)
    (e0 : (g ⟨0, by norm_num⟩ : ℕ) = h ⟨0, by norm_num⟩)
    (e1 : (g ⟨1, by norm_num⟩ : ℕ) = h ⟨1, by norm_num⟩)
    (e9 : (g ⟨9, by norm_num⟩ : ℕ) = h ⟨9, by norm_num⟩)
    (e84 : (g ⟨84, by norm_num⟩ : ℕ) = h ⟨84, by norm_num⟩) : g = h := by
  have key : ∀ b : Fin 820, (g b : ℕ) = h b → (h⁻¹ * g) b = b := fun b e => by
    rw [Equiv.Perm.mul_apply, Fin.ext e, ← Equiv.Perm.mul_apply, inv_mul_cancel,
      Equiv.Perm.one_apply]
  have := fix_one (Nrm.mul_mem (Nrm.inv_mem hh) hg) (key _ e0) (key _ e1) (key _ e9) (key _ e84)
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem sep4inv (g h : Gp) (hg : g ∈ Nrm) (hh : h ∈ Nrm)
    (e0 : (g⁻¹ ⟨0, by norm_num⟩ : ℕ) = h⁻¹ ⟨0, by norm_num⟩)
    (e1 : (g⁻¹ ⟨1, by norm_num⟩ : ℕ) = h⁻¹ ⟨1, by norm_num⟩)
    (e9 : (g⁻¹ ⟨9, by norm_num⟩ : ℕ) = h⁻¹ ⟨9, by norm_num⟩)
    (e84 : (g⁻¹ ⟨84, by norm_num⟩ : ℕ) = h⁻¹ ⟨84, by norm_num⟩) : g = h :=
  inv_injective (sep4 (Nrm.inv_mem hg) (Nrm.inv_mem hh) e0 e1 e9 e84)

theorem tGensG_len5 : tGensG.length = 5 := by
  rw [tGensG_len, pGenIdx_len]
  rfl

theorem tGensG_lo {j : ℕ} (hj : j < 3) : tGensG.getD j 1 = psi (hElt (pIdx j)) := by
  interval_cases j <;> rfl

theorem tGensG_hi {e : ℕ} (he : e < 2) : tGensG.getD (3 + e) 1 = wordP (tExtraWords.getD e []) := by
  interval_cases e <;> rfl

theorem TT_lo {j : ℕ} (hj : j < 3) (q : ℕ) (hq : q < 820) :
    pg 10 1023 (TT (2 * j + 1)) q = (tGensG.getD j 1 ⟨q, hq⟩ : ℕ) ∧
      pg 10 1023 (TT (2 * j)) q = ((tGensG.getD j 1)⁻¹ ⟨q, hq⟩ : ℕ) := by
  have h := allN_spec (allN_spec kTP j hj) q hq
  have e : Nat.shiftLeft j 1 = 2 * j := by
    change j <<< 1 = 2 * j
    rw [Nat.shiftLeft_eq]
    ring
  rw [e, bAnd_iff, beq_iff, beq_iff] at h
  have hi : pIdx j < 1152 := pGenIdx_lt _ hj
  rw [tGensG_lo hj]
  refine ⟨h.1.trans (EH_eq hi q hq).1, ?_⟩
  rw [← map_inv]
  exact h.2.trans (EH_eq hi q hq).2

theorem cosI_mem (c : ℕ) : ∃ y ∈ Nrm, PRep 820 10 (cosI c) y := by
  have hdI : ∀ m, PRep 820 10 (dIPow m) (dPerm⁻¹ ^ m) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero]
      exact prep_pidn (by norm_num) (by norm_num)
    | succ m ih =>
      rw [pow_succ']
      exact prep_pcomp KernelU43Aut3962.hn32 KernelU43Aut3962.prep_d.2 ih
  have hd : dPerm⁻¹ ∈ Nrm := Nrm.inv_mem (dPerm_mem autFacts)
  unfold cosI
  cases Nat.beq (Nat.land c 1) 0
  · exact ⟨sPerm⁻¹ * dPerm⁻¹ ^ (Nat.shiftRight c 1),
      Nrm.mul_mem (Nrm.inv_mem (sPerm_mem autFacts)) (Nrm.pow_mem hd _),
      prep_pcomp KernelU43Aut3962.hn32 KernelU43Aut3962.prep_s.2 (hdI _)⟩
  · exact ⟨1 * dPerm⁻¹ ^ (Nat.shiftRight c 1), Nrm.mul_mem Nrm.one_mem (Nrm.pow_mem hd _),
      prep_pcomp KernelU43Aut3962.hn32 (prep_pidn (by norm_num) (by norm_num)) (hdI _)⟩

theorem xgen {A B c : ℕ} {w : List ℕ} (hp : permOK 820 10 (mask 10) (820 * 10) A B = true)
    (hin : KernelU43Aut3962.inN (KernelU43Aut3962.pc A (cosI c)) = true)
    (hb : CFSG.KC.U43Mod.baseEq bs4 (pg 10 1023 A) (mwv LP8 w) = true) (q : ℕ) (hq : q < 820) :
    pg 10 1023 A q = (wordP w ⟨q, hq⟩ : ℕ) ∧ pg 10 1023 B q = ((wordP w)⁻¹ ⟨q, hq⟩ : ℕ) := by
  have hr := rep_permOfArr (isInvA_unpack hp)
  have hX : PRep 820 10 A (permOfArr 820 (unpack 820 10 A)) := prep_of_rep hr.1
  have hXi : PRep 820 10 B (permOfArr 820 (unpack 820 10 A))⁻¹ := prep_of_rep hr.2
  obtain ⟨y, hy, hyp⟩ := cosI_mem c
  have hXy := KernelU43Aut3962.mem_of_inN (prep_pcomp KernelU43Aut3962.hn32 hX hyp) hin
  have hXN : permOfArr 820 (unpack 820 10 A) ∈ Nrm := by
    have := Nrm.mul_mem (Nsub_le_Nrm hXy) (Nrm.inv_mem hy)
    rwa [mul_inv_cancel_right] at this
  have hb' : bAnd(Nat.beq (pg 10 1023 A 0) (mwv LP8 w 0), bAnd(Nat.beq (pg 10 1023 A 1)
      (mwv LP8 w 1), bAnd(Nat.beq (pg 10 1023 A 9) (mwv LP8 w 9), bAnd(Nat.beq (pg 10 1023 A 84)
      (mwv LP8 w 84), true)))) = true := hb
  simp only [bAnd_iff, beq_iff] at hb'
  obtain ⟨b0, b1, b9, b84, -⟩ := hb'
  have hpt : ∀ p (hp : p < 820), pg 10 1023 A p = (permOfArr 820 (unpack 820 10 A) ⟨p, hp⟩ : ℕ) :=
    fun p hp => hX ⟨p, hp⟩
  have heq : permOfArr 820 (unpack 820 10 A) = wordP w := sep4 hXN (wordP_mem autFacts w)
    (by rw [← hpt 0 (by norm_num), b0, mwv8_eq w 0 (by norm_num)])
    (by rw [← hpt 1 (by norm_num), b1, mwv8_eq w 1 (by norm_num)])
    (by rw [← hpt 9 (by norm_num), b9, mwv8_eq w 9 (by norm_num)])
    (by rw [← hpt 84 (by norm_num), b84, mwv8_eq w 84 (by norm_num)])
  rw [← heq]
  exact ⟨hX ⟨q, hq⟩, hXi ⟨q, hq⟩⟩

theorem TT_hi {e : ℕ} (he : e < 2) (q : ℕ) (hq : q < 820) :
    pg 10 1023 (TT (2 * (3 + e) + 1)) q = (tGensG.getD (3 + e) 1 ⟨q, hq⟩ : ℕ) ∧
      pg 10 1023 (TT (2 * (3 + e))) q = ((tGensG.getD (3 + e) 1)⁻¹ ⟨q, hq⟩ : ℕ) := by
  rw [tGensG_hi he, ← CFSG.KS.U43Aut3962.lSel_eq]
  have h := allN_spec kTX e he
  unfold xRec at h
  rw [sbEq, bAnd_iff, bAnd_iff] at h
  interval_cases e
  · exact xgen h.1 h.2.1 h.2.2 q hq
  · exact xgen h.1 h.2.1 h.2.2 q hq

theorem TT_eq {j : ℕ} (hj : j < 5) (q : ℕ) (hq : q < 820) :
    pg 10 1023 (TT (2 * j + 1)) q = (tGensG.getD j 1 ⟨q, hq⟩ : ℕ) ∧
      pg 10 1023 (TT (2 * j)) q = ((tGensG.getD j 1)⁻¹ ⟨q, hq⟩ : ℕ) := by
  by_cases h3 : j < 3
  · exact TT_lo h3 q hq
  · obtain ⟨e, rfl⟩ : ∃ e, j = 3 + e := ⟨j - 3, by omega⟩
    exact TT_hi (by omega) q hq

theorem xor_one_even5 {j : ℕ} (hj : j < 5) : Nat.xor (2 * j) 1 = 2 * j + 1 := by
  interval_cases j <;> rfl

theorem xor_one_odd5 {j : ℕ} (hj : j < 5) : Nat.xor (2 * j + 1) 1 = 2 * j := by
  interval_cases j <;> rfl

theorem hG_T : ∀ l < 10, ∀ q (hq : q < 820), GkT l q = ((sFP tGensG l)⁻¹ ⟨q, hq⟩ : ℕ) ∧
    GrT l q = (sFP tGensG l ⟨q, hq⟩ : ℕ) := by
  intro l hl q hq
  obtain ⟨j, ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩⟩ := half_cases (l := l)
  · have hj : j < 5 := by omega
    unfold GkT GrT sFP
    rw [if_pos h1, h2, xor_one_even5 hj]
    exact ⟨(TT_eq hj q hq).2, (TT_eq hj q hq).1⟩
  · have hj : j < 5 := by omega
    unfold GkT GrT sFP
    rw [if_neg (by omega), h2, xor_one_odd5 hj, inv_inv]
    exact ⟨(TT_eq hj q hq).1, (TT_eq hj q hq).2⟩

theorem tElt_eq (k : ℕ) : tElt k = treeP 1 (mulStepP tGensG) tPar tLab 10 fuel k := by
  unfold tElt
  rw [tGensG_len5]

theorem tElt_zero : tElt 0 = 1 := by simp [tElt, treeP, fuel]

theorem tFacts : ∀ k < 1024, KeyOf4 (TR k) (tElt k)⁻¹ ∧ WalkOfP TR GrT GkT k (tElt k) := by
  intro k hk
  rw [tElt_eq]
  exact key_tree4 hG_T (by norm_num) kTtree kT4 (fldsAre_spec kTpar) (fldsAre_spec kTlab) k hk

theorem ET_eq {k : ℕ} (hk : k < 1024) (q : ℕ) (hq : q < 820) :
    ET k q = (tElt k ⟨q, hq⟩ : ℕ) ∧ ETi k q = ((tElt k)⁻¹ ⟨q, hq⟩ : ℕ) :=
  (tFacts k hk).2 32 (kdep_le kTtree k hk) q hq

theorem tElt_mem (k : ℕ) : tElt k ∈ tSub := by
  have hnl : 0 < 2 * tGensG.length := by rw [tGensG_len5]; norm_num
  unfold tElt
  refine treeP_mem (Q := (· ∈ tSub)) (one_mem _) hnl (fun g l hl hg => ?_) tPar tLab fuel k
  have hj : l / 2 < tGensG.length := by omega
  have hy : tGensG.getD (l / 2) 1 ∈ tSub := by
    apply Subgroup.subset_closure
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  unfold mulStepP
  split_ifs
  · exact mul_mem hg hy
  · exact mul_mem hg (inv_mem hy)

theorem tElt_Nrm (k : ℕ) : tElt k ∈ Nrm := tSub_le_Nrm autFacts (tElt_mem k)

theorem sFP_Nrm {l : ℕ} (hl : l < 10) : sFP tGensG l ∈ Nrm := by
  have hj : l / 2 < tGensG.length := by rw [tGensG_len5]; omega
  have hy : tGensG.getD (l / 2) 1 ∈ Nrm := by
    apply tSub_le_Nrm autFacts
    apply Subgroup.subset_closure
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  unfold sFP
  split_ifs
  · exact hy
  · exact Nrm.inv_mem hy

theorem inv_fact : ∀ j < tGens.length, isInvA 820 tGens[j]! (invCand 820 tGens[j]!) = true :=
  fun j hj => isInvA_invCand (rep_tGens autFacts j (by rw [← tGens_length]; exact hj))

theorem rep_tTab' (k : ℕ) : Rep 820 (tTab k) (tElt k) := by
  have hnl : 0 < 2 * tGensG.length := by rw [tGensG_len5]; norm_num
  unfold tTab tElt
  rw [tGens_length]
  exact rep_treeP rep_idA hnl (fun t g l hl h => rep_mulStepP tGens_length (rep_tGens autFacts)
    (fun j hj => inv_fact j (by rw [tGens_length]; exact hj)) t g l hl h) tPar tLab fuel k

theorem clos : ∀ k < 1024, ∀ l < 10,
    tTbl[k * 10 + l]! < 1024 ∧ tElt tTbl[k * 10 + l]! = tElt k * sFP tGensG l :=
  key_clos4 (Q := (· ∈ Nrm)) (by norm_num) (fun k hk => (tFacts k hk).1)
    (fun l hl q hq => (hG_T l hl q hq).1) (fun k _ => tElt_Nrm k)
    (fun k _ l hl => Nrm.mul_mem (tElt_Nrm k) (sFP_Nrm hl)) sep4inv kTclos

theorem closed_fact : closedOK tTab tTbl 1024 (2 * tGens.length) (mulStep tGens) = true := by
  have e : 2 * tGens.length = 10 := by rw [tGens_length, tGensG_len5]
  rw [e]
  refine closedOK_of (x := tElt) (sG := fun p l => p * sFP tGensG l) (fun k _ => rep_tTab' k)
    (fun k _ l hl => ?_) clos
  have h := rep_mulStepP tGens_length (rep_tGens autFacts)
    (fun j hj => inv_fact j (by rw [tGens_length]; exact hj)) (tTab k) (tElt k) l
    (by rw [tGensG_len5]; exact hl) (rep_tTab' k)
  rwa [mulStepP_eq] at h

theorem tSurj : ∀ h ∈ tSub, ∃ k < 1024, tElt k = h := by
  intro h hh
  induction hh using Subgroup.closure_induction_right with
  | one => exact ⟨0, by norm_num, tElt_zero⟩
  | mul_right x hx y hy ih =>
    obtain ⟨k, hk, rfl⟩ := ih
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    have hj5 : j < 5 := by rw [← tGensG_len5]; exact hj
    obtain ⟨h1, h2⟩ := clos k hk (2 * j) (by omega)
    refine ⟨_, h1, ?_⟩
    rw [h2]
    have e1 : (2 * j) % 2 = 0 := by omega
    have e2 : (2 * j) / 2 = j := by omega
    simp [sFP, e1, e2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨k, hk, rfl⟩ := ih
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    have hj5 : j < 5 := by rw [← tGensG_len5]; exact hj
    obtain ⟨h1, h2⟩ := clos k hk (2 * j + 1) (by omega)
    refine ⟨_, h1, ?_⟩
    rw [h2]
    have e1 : (2 * j + 1) % 2 = 1 := by omega
    have e2 : (2 * j + 1) / 2 = j := by omega
    simp [sFP, e1, e2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem tinj_key {i j : ℕ} (hi : i < 1024) (hj : j < 1024)
    (h0 : ((tElt i)⁻¹ ⟨0, by norm_num⟩ : ℕ) = (tElt j)⁻¹ ⟨0, by norm_num⟩)
    (h1 : ((tElt i)⁻¹ ⟨1, by norm_num⟩ : ℕ) = (tElt j)⁻¹ ⟨1, by norm_num⟩)
    (h9 : ((tElt i)⁻¹ ⟨9, by norm_num⟩ : ℕ) = (tElt j)⁻¹ ⟨9, by norm_num⟩) : i = j :=
  key_inj4 (by norm_num) (fun k hk => (tFacts k hk).1) kTord hi hj h0 h1 h9

theorem dist_fact : distinctOK tTab 1024 = true := by
  refine distinctOK_of (x := tElt) (fun k _ => rep_tTab' k) fun i hi j hj e0 e1 e9 => ?_
  have hfix : ∀ b : Fin 820, tElt i b = tElt j b → ((tElt j)⁻¹ * tElt i)⁻¹ b = b := by
    intro b e
    rw [Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.mul_apply, e, ← Equiv.Perm.mul_apply, inv_mul_cancel,
      Equiv.Perm.one_apply]
  obtain ⟨m, hm, hme⟩ := tSurj _ (mul_mem (inv_mem (tElt_mem j)) (tElt_mem i))
  have hm0 : m = 0 := tinj_key hm (by norm_num)
    (by rw [hme, hfix _ e0, tElt_zero]; simp) (by rw [hme, hfix _ e1, tElt_zero]; simp)
    (by rw [hme, hfix _ e9, tElt_zero]; simp)
  have hij : tElt j = tElt i := by
    rw [hm0, tElt_zero] at hme
    exact inv_mul_eq_one.1 hme.symm
  exact tinj_key hi hj (by rw [hij]) (by rw [hij]) (by rw [hij])

theorem witWords_lt : ∀ w ∈ witWords, ∀ l ∈ w, l < 4 := by decide

theorem uPt_eq {k : ℕ} (hk : k < 1024) {w : List ℕ} (hw : ∀ l ∈ w, l < 4) (p : ℕ) (hp : p < 820) :
    uPt k w p = ((tElt k * (psi (wordElt w) * tElt k * (psi (wordElt w))⁻¹)) ⟨p, hp⟩ : ℕ) := by
  unfold uPt
  rw [mwvI_eq LP_eq w hw p hp, (ET_eq hk _ (Fin.is_lt _)).1, Fin.eta,
    mwv_eq LP_eq w _ (Fin.is_lt _), Fin.eta, (ET_eq hk _ (Fin.is_lt _)).1, Fin.eta]
  simp only [Equiv.Perm.mul_apply, map_inv]

theorem five_lt_of_orb {u : Gp} {f : ℕ → ℕ} {q : ℕ} (hq : q < 820)
    (hf : ∀ m, f^[m] q = ((u ^ m) ⟨q, hq⟩ : ℕ)) (ho : orbOK f q 5 q = true) : 5 < orderOf u := by
  have hne := orbOK_spec 5 q ho
  by_contra hle
  push Not at hle
  have hpos := orderOf_pos u
  have hlt : orderOf u - 1 < 5 := by omega
  apply hne _ hlt
  rw [Nat.sub_add_cancel hpos, hf, pow_orderOf_eq_one]
  rfl

theorem wit_ns {k : ℕ} (hk : k < 1024) {i q : ℕ} (h : witOK k i q = true) :
    ∃ w ∈ witWords, 5 < orderOf (tElt k * (psi (wordElt w) * tElt k * (psi (wordElt w))⁻¹)) := by
  unfold witOK at h
  rw [bAnd_iff, blt_iff, bAnd_iff, blt_iff] at h
  obtain ⟨hi, hq, ho⟩ := h
  have hi3 : i < 3 := hi
  have hi' : i < witWords.length := by
    have : witWords.length = 3 := rfl
    omega
  rw [CFSG.KS.U43Aut3962.lSel_eq] at ho
  have hw : witWords.getD i [] ∈ witWords := by
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  refine ⟨_, hw, five_lt_of_orb hq (fun m => ?_) ho⟩
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, uPt_eq hk (witWords_lt _ hw) _ (Fin.is_lt _), Fin.eta,
      pow_succ', Equiv.Perm.mul_apply _ (_ ^ m)]

theorem nonSmall_of {t : Array ℕ} {τ : Gp} (ht : Rep 820 t τ)
    (h : ∃ w ∈ witWords, 5 < orderOf (τ * (psi (wordElt w) * τ * (psi (wordElt w))⁻¹))) :
    nonSmall t = true := by
  obtain ⟨w, hw, ho⟩ := h
  have hg : Rep 820 (wordTab w) (psi (wordElt w)) := rep_wordTab w
  have hu : Rep 820 (compA 820 t (conjTab (wordTab w) t))
      (τ * (psi (wordElt w) * τ * (psi (wordElt w))⁻¹)) :=
    rep_compA ht (rep_conjTab hg ht (rep_invCand hg))
  unfold nonSmall
  rw [List.any_eq_true]
  refine ⟨w, hw, ?_⟩
  dsimp only
  rw [List.all_eq_true]
  intro k hk
  have hk' : 0 < k ∧ k ≤ 5 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, eqA_iff (rep_powTab_perm hu k) rep_idA]
  intro e
  have := orderOf_le_of_pow_eq_one hk'.1 e
  omega

theorem fRec_cases {k : ℕ} (hk : k < 1024) :
    (Nat.land (FR k) (nat_lit 3) = 0 ∧ innerOK k (Nat.shiftRight (FR k) (nat_lit 2)) = true) ∨
    (Nat.land (FR k) (nat_lit 3) = 1 ∧ Nat.shiftRight (FR k) (nat_lit 2) < 820 ∧
      ET k (ET k (Nat.shiftRight (FR k) (nat_lit 2))) ≠ Nat.shiftRight (FR k) (nat_lit 2)) ∨
    (Nat.land (FR k) (nat_lit 3) = 2 ∧ witOK k (Nat.land (Nat.shiftRight (FR k) (nat_lit 2)) (nat_lit 3))
      (Nat.shiftRight (Nat.shiftRight (FR k) (nat_lit 2)) (nat_lit 2)) = true) ∨
    (Nat.land (FR k) (nat_lit 3) ≠ 0 ∧ Nat.land (FR k) (nat_lit 3) ≠ 2 ∧
      Nat.shiftRight (FR k) (nat_lit 2) < 24 ∧ SK (Nat.shiftRight (FR k) (nat_lit 2)) = k) := by
  have h := allN_spec kF k hk
  unfold fRec at h
  rw [sbEq, sbEq, sbEq] at h
  generalize Nat.shiftRight (FR k) (nat_lit 2) = x at h ⊢
  generalize Nat.land (FR k) (nat_lit 3) = t at h ⊢
  cases h0 : Nat.beq t 0 <;> rw [h0] at h <;> dsimp only at h
  · have t0 : t ≠ 0 := beq_false_iff.1 h0
    cases h1 : Nat.beq t 1 <;> rw [h1] at h <;> dsimp only at h
    · cases h2 : Nat.beq t 2 <;> rw [h2] at h <;> dsimp only at h
      · simp only [bAnd_iff, blt_iff, beq_iff] at h
        exact Or.inr (Or.inr (Or.inr ⟨t0, beq_false_iff.1 h2, h⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨beq_iff.1 h2, h⟩))
    · simp only [bAnd_iff, blt_iff, bNot_iff, beq_false_iff] at h
      exact Or.inr (Or.inl ⟨beq_iff.1 h1, h⟩)
  · exact Or.inl ⟨beq_iff.1 h0, h⟩

theorem inner_mem {k j : ℕ} (hk : k < 1024) (h : innerOK k j = true) : tElt k ∈ Nsub := by
  unfold innerOK at h
  rw [bAnd_iff, blt_iff, sbEq, sbEq] at h
  obtain ⟨hj, h⟩ := h
  simp only [bAnd_iff, beq_iff] at h
  obtain ⟨e0, e1, e2, e3⟩ := h
  obtain ⟨⟨t0, t1, t9, t84⟩, -⟩ := tFacts k hk
  obtain ⟨⟨p0, p1, p9⟩, pw⟩ := pFacts j hj
  have hw : EPi j 84 = (psi (pElt j)⁻¹ ⟨84, by norm_num⟩ : ℕ) :=
    (pw 32 (kdep_le kPtree j hj) 84 (by norm_num)).2
  have hp : psi (pElt j) ∈ Nrm := Nsub_le_Nrm ⟨_, rfl⟩
  have heq := sep4inv _ _ (tElt_Nrm k) hp
    (by rw [← t0, e0, p0, map_inv]) (by rw [← t1, e1, p1, map_inv]) (by rw [← t9, e2, p9, map_inv])
    (by rw [← t84, e3, hw, map_inv])
  rw [heq]
  exact ⟨_, rfl⟩

theorem pRec_cases {k₁ k₂ d : ℕ} (h : pRec FR k₁ k₂ d = true) :
    (∃ x < 820, ET k₁ (ET k₂ x) ≠ ET k₂ (ET k₁ x)) ∨
    (∃ x < 1024, (Nat.land (FR x) (nat_lit 3) = 0 ∨ Nat.land (FR x) (nat_lit 3) = 2) ∧
      prodKey k₁ k₂ (TR x) = true) := by
  unfold pRec at h
  rw [sbEq, sbEq] at h
  generalize Nat.shiftRight d (nat_lit 2) = x at h
  generalize Nat.land d (nat_lit 3) = t at h
  cases h0 : Nat.beq t 0 <;> rw [h0] at h <;> dsimp only at h
  · rw [bAnd_iff, bAnd_iff, blt_iff, sbEq, bAnd_iff] at h
    obtain ⟨-, hx, h1, h2⟩ := h
    refine Or.inr ⟨x, hx, ?_, h2⟩
    cases h3 : Nat.beq (Nat.land (FR x) (nat_lit 3)) 0 <;> rw [h3] at h1 <;> dsimp only at h1
    · exact Or.inr (beq_iff.1 h1)
    · exact Or.inl (beq_iff.1 h3)
  · rw [bAnd_iff, blt_iff, bNot_iff, beq_false_iff] at h
    exact Or.inl ⟨x, h.1, h.2⟩

theorem prod_eq {k₁ k₂ m : ℕ} (h1 : k₁ < 1024) (h2 : k₂ < 1024) (hm : m < 1024)
    (h : prodKey k₁ k₂ (TR m) = true) : tElt m = tElt k₁ * tElt k₂ := by
  unfold prodKey at h
  simp only [bAnd_iff, beq_iff] at h
  obtain ⟨e0, e1, e2, e3⟩ := h
  obtain ⟨⟨t0, t1, t9, t84⟩, -⟩ := tFacts m hm
  have hpt : ∀ q (hq : q < 820), ETi k₂ (ETi k₁ q) = ((tElt k₁ * tElt k₂)⁻¹ ⟨q, hq⟩ : ℕ) := by
    intro q hq
    rw [(ET_eq h1 q hq).2, (ET_eq h2 _ (Fin.is_lt _)).2, Fin.eta, mul_inv_rev, Equiv.Perm.mul_apply]
  exact sep4inv _ _ (tElt_Nrm m) (Nrm.mul_mem (tElt_Nrm k₁) (tElt_Nrm k₂))
    (by rw [← t0, e0, hpt 0 (by norm_num)]) (by rw [← t1, e1, hpt 1 (by norm_num)])
    (by rw [← t9, e2, hpt 9 (by norm_num)]) (by rw [← t84, e3, hpt 84 (by norm_num)])

theorem outer_cases {k : ℕ} (hk : k < 1024) (hi : isInvol (tTab k) = true)
    (hm : memNA (tTab k) = false) :
    (∃ w ∈ witWords, 5 < orderOf (tElt k * (psi (wordElt w) * tElt k * (psi (wordElt w))⁻¹))) ∨
      ∃ s < 24, SK s = k := by
  rcases fRec_cases hk with ⟨-, h⟩ | ⟨-, hq, hne⟩ | ⟨-, h⟩ | ⟨-, -, h⟩
  · rw [(memNA_iff (rep_tTab' k)).2 (inner_mem hk h)] at hm
    exact absurd hm (by decide)
  · exfalso
    apply hne
    have h2 := ((isInvol_iff_P (rep_tTab' k)).1 hi).1
    rw [(ET_eq hk _ hq).1, (ET_eq hk _ (Fin.is_lt _)).1, Fin.eta, ← Equiv.Perm.mul_apply, h2]
    rfl
  · exact Or.inl (wit_ns hk h)
  · exact Or.inr ⟨_, h.1, h.2⟩

theorem pairs_fact : ∀ k₁ < 1024, ∀ k₂ < 1024, isInvol (tTab k₁) = true →
    memNA (tTab k₁) = false → isInvol (tTab k₂) = true → memNA (tTab k₂) = false →
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out.pairOK memNA (tTab k₁) (tTab k₂) = true := by
  intro k₁ hk₁ k₂ hk₂ hi₁ hm₁ hi₂ hm₂
  have r1 := rep_tTab' k₁
  have r2 := rep_tTab' k₂
  have r12 := rep_compA r1 r2
  unfold CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out.pairOK
  simp only [Bool.or_eq_true]
  rcases outer_cases hk₁ hi₁ hm₁ with h1 | ⟨s₁, hs₁, e₁⟩
  · exact Or.inl (Or.inl (Or.inr (nonSmall_of r1 h1)))
  rcases outer_cases hk₂ hi₂ hm₂ with h2 | ⟨s₂, hs₂, e₂⟩
  · exact Or.inl (Or.inr (nonSmall_of r2 h2))
  have hp := allN_spec kPW (s₁ * 24 + s₂) (by omega)
  have d1 : Nat.div (s₁ * 24 + s₂) 24 = s₁ := by
    change (s₁ * 24 + s₂) / 24 = s₁
    omega
  have d2 : Nat.mod (s₁ * 24 + s₂) 24 = s₂ := by
    change (s₁ * 24 + s₂) % 24 = s₂
    omega
  rw [d1, d2, e₁, e₂] at hp
  rcases pRec_cases hp with ⟨x, hx, hne⟩ | ⟨m, hm, ht, hkey⟩
  · refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, eqA_iff r12 (rep_compA r2 r1)]
    intro e
    apply hne
    rw [(ET_eq hk₂ _ hx).1, (ET_eq hk₁ _ (Fin.is_lt _)).1, Fin.eta, (ET_eq hk₁ _ hx).1,
      (ET_eq hk₂ _ (Fin.is_lt _)).1, Fin.eta, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, e]
  · rw [← prod_eq hk₁ hk₂ hm hkey] at r12
    rcases fRec_cases hm with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, h', -⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inr ((memNA_iff r12).2 (inner_mem hm h)))))
    · exfalso
      rcases ht with ht | ht <;> omega
    · exact Or.inr (nonSmall_of r12 (wit_ns hm h))
    · exfalso
      rcases ht with ht | ht <;> omega

theorem pos_fact : 0 < tGens.length := by
  rw [tGens_length, tGensG_len5]
  norm_num

theorem wit_fact : ∀ w ∈ witWords, isInvA 820 (wordTab w) (invCand 820 (wordTab w)) = true :=
  fun w _ => isInvA_invCand (rep_wordTab w)

theorem outFacts' : OutFacts :=
  ⟨pos_fact, inv_fact, dist_fact, closed_fact, wit_fact, pairs_fact⟩

theorem u43OutCheck_ok : u43OutCheck () = true := u43OutCheck_of outFacts'

end CertificateChecks.KernelU43Out

end
