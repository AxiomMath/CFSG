
module

public import Certificates.Kernel.J4Q.D4K
public import CFSG.Certificates.Kernel.J4FiveSound
public import Certificates.Kernel.J4Count.ChecksFive
public import Certificates.Kernel.J4Count.SuborbBase

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Five

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.J4.Struct CertificateChecks.KernelSporSch
open CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.Native CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4Five
open CertificateChecks.KernelJ4Q CFSG.QuasithinUnique.A5
open scoped Classical

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hM5 : MatFacts := CertificateChecks.KernelJ4Q.matFacts

theorem conj_sq_of_coe {G : Type*} [Group G] {K : Subgroup G} {a b : K}
    (h : (a : G) * b * (a : G)⁻¹ = (b : G) ^ 2) : a * b * a⁻¹ = b ^ 2 :=
  Subtype.ext (by simpa using h)

noncomputable abbrev pV (i : ℕ) : V2 := d4Pts.getD i V2.zero

noncomputable abbrev ptsV (i : ℕ) : Row := toRow (pV i).toVec

theorem d4Pts_length : d4Pts.length = 14 := by
  rw [← List.length_map (f := v2N), d4pts_map]
  rfl

theorem pV_eq {i : ℕ} (hi : i < 14) : pV i = d4Pts[i]'(by rw [d4Pts_length]; exact hi) := by
  unfold pV
  exact List.getD_eq_getElem _ _ _

theorem pV_mem {i : ℕ} (hi : i < 14) : pV i ∈ d4Pts := by
  rw [pV_eq hi]
  exact List.getElem_mem _

theorem pV_wf {i : ℕ} (hi : i < 14) : (pV i).wf = true := d4pts_wf _ (pV_mem hi)

theorem XPTS_length : XPTS.length = 14 := rfl

theorem v2N_pV {i : ℕ} (hi : i < 14) : v2N (pV i) = getN 0 XPTS i := by
  have hl : i < (d4Pts.map v2N).length := by rw [List.length_map, d4Pts_length]; exact hi
  rw [getN_getD, List.getD_eq_getElem _ _ (by rw [XPTS_length]; exact hi)]
  simp only [← d4pts_map, List.getElem_map, pV_eq hi]

theorem ptsV_inj {i j : ℕ} (hi : i < 14) (hj : j < 14) (h : ptsV i = ptsV j) : i = j := by
  have h1 : pV i = pV j := (V2.toVec_inj (pV_wf hi) (pV_wf hj)).1 (congrArg ofRow h)
  have h2 := congrArg v2N h1
  rw [v2N_pV hi, v2N_pV hj] at h2
  have hnd : XPTS.Nodup := distB_spec pts_dist
  rw [getN_getD, getN_getD, List.getD_eq_getElem _ _ (by rw [XPTS_length]; exact hi),
    List.getD_eq_getElem _ _ (by rw [XPTS_length]; exact hj)] at h2
  exact (List.Nodup.getElem_inj_iff hnd).1 h2

theorem mem_pts_iff {p : Row} : p ∈ x0PtSet ↔ ∃ i < 14, p = ptsV i := by
  unfold x0PtSet
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (show d ∈ d4Pts from hd)
    have hi' : i < 14 := by rw [← d4Pts_length]; exact hi
    refine ⟨i, hi', ?_⟩
    unfold ptsV
    rw [pV_eq hi']
  · rintro ⟨i, hi, rfl⟩
    exact ⟨pV i, pV_mem hi, rfl⟩

theorem toVec_eq_toVecD (p : V2) : p.toVec = toVecD 112 (v2N p) := by
  funext j
  rw [V2.toVec_apply, toVecD_apply, testBit_v2N p (by omega)]

theorem ptsV_eq {i : ℕ} (hi : i < 14) : ptsV i = toRow (toVecD 112 (getN 0 XPTS i)) := by
  unfold ptsV
  rw [toVec_eq_toVecD, v2N_pV hi]

theorem ptsV_zero : ptsV 0 = v := by
  have h : pV 0 = rootV := v2N_inj (by rw [v2N_pV (by norm_num)]; exact Nat.eq_of_beq_eq_true pts_root)
  unfold ptsV
  rw [h, v_eq_root]

section Act

theorem inv_smul_ptsV {l i j : ℕ} (hl : l < 16) (hi : i < 14) (hj : j < 14)
    (h : vecJ rm (getN 0 XPTS i) (getN one XG l) = getN 0 XPTS j) :
    (x0Gen l)⁻¹ • ptsV i = ptsV j := by
  have he := x0All_enc hl
  have hv : v2N (frApply (frTable (x0AllRows[l]!)) (pV i)) = v2N (pV j) := by
    rw [v2N_frApply hK he.1 (pV_wf hi), he.2, v2N_pV hi, v2N_pV hj, h]
  have e := v2N_inj hv
  rw [← ofRow_inj, inv_smul_row, ← QT.Mx_apply, Mx_x0Gen hM5 hl]
  change Matrix.vecMul (pV i).toVec (CFSG.Sporadic.J4.rowsMatrix (x0AllRows[l]!)) = (pV j).toVec
  rw [← e, frApply_toVec_eq_vecMul]

def BlockOK (g : J) : Prop :=
  ∀ i < 14, ∃ j < 14, g • ptsV i = ptsV j ∧ g • ptsV (getN 0 PHI i) = ptsV (getN 0 PHI j)

theorem phi_lt' {i : ℕ} (hi : i < 14) : getN 0 PHI i < 14 :=
  Nat.le_of_ble_eq_true (allN_spec phi_lt i hi)

theorem block_inv_gen {l : ℕ} (hl : l < 16) : BlockOK (x0Gen l)⁻¹ := by
  intro i hi
  obtain ⟨j, hj, h1, h2⟩ := eqvOK_spec (by decide) pts_eqv l hl i hi
  exact ⟨j, hj, inv_smul_ptsV hl hi hj h1, inv_smul_ptsV hl (phi_lt' hi) (phi_lt' hj) h2⟩

theorem block_gen {l : ℕ} (hl : l < 16) : BlockOK (x0Gen l) := by
  have e : x0Gen l = (x0Gen ((l + 8) % 16))⁻¹ := by
    rw [x0Gen_inv (Nat.mod_lt _ (by norm_num))]
    congr 1
    omega
  rw [e]
  exact block_inv_gen (Nat.mod_lt _ (by norm_num))

theorem block_mul {g h : J} (hg : BlockOK g) (hh : BlockOK h) : BlockOK (g * h) := by
  intro i hi
  obtain ⟨j, hj, e1, e2⟩ := hh i hi
  obtain ⟨k, hk, e3, e4⟩ := hg j hj
  exact ⟨k, hk, by rw [mul_smul, e1, e3], by rw [mul_smul, e2, e4]⟩

theorem block_closure {g : J} (hg : g ∈ X0Sub) : BlockOK g := by
  have : Finite J := KernelJ4Hub.finite_J
  have hg' : g ∈ (X0Sub : Subgroup J).toSubmonoid := hg
  rw [X0Sub, Subgroup.closure_toSubmonoid_of_finite] at hg'
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact block_gen hl
  | one => exact fun i hi => ⟨i, hi, one_smul _ _, one_smul _ _⟩
  | mul x y _ _ hx hy => exact block_mul hx hy

noncomputable abbrev qA : Row := ptsV 1

theorem S_fix_qA {g : J} (hg : g ∈ X0Sub) (hv : g • v = v) : g • qA = qA := by
  obtain ⟨j, hj, e1, e2⟩ := block_closure hg 0 (by norm_num)
  rw [ptsV_zero, hv, ← ptsV_zero] at e1
  have hj0 := ptsV_inj (i := j) (j := 0) hj (by norm_num) e1.symm
  subst hj0
  exact e2

theorem qA_mem_pts : qA ∈ x0PtSet := mem_pts_iff.2 ⟨1, by norm_num, rfl⟩

theorem qA_ne_v : qA ≠ v := by
  rw [← ptsV_zero]
  intro h
  exact absurd (ptsV_inj (by norm_num) (by norm_num) h) (by norm_num)

end Act

theorem g5_gens (k : Nat) : WfA ((QT2A.g5Mats ())[k]?.getD (idRows ())) ∧
    encR ((QT2A.g5Mats ())[k]?.getD (idRows ())) = getN one G5L k :=
  gens_append locMats_size loc_gens base_gens k

theorem g5_invs (k : Nat) : WfA ((QT2A.g5Invs ())[k]?.getD (idRows ())) ∧
    encR ((QT2A.g5Invs ())[k]?.getD (idRows ())) = getN one G5iL k :=
  gens_append locInvs_size loc_invs base_invs k

theorem nVec_spec {p : V2} (hp : p.wf = true) :
    v2N (frApply (frTable nRows) p) = nVec (v2N p) := by
  have hU := (wR_enc nWordU).1
  have hE := (eta_enc nMask).1
  have hV := (wR_enc nWordV).1
  have hp1 := wf_frApply hU p
  have h1 := vwK_wordRows hK g5_gens g5_invs nWordU hp
  have h2 := etaVec_enc hp1 nMask
  have h3 := vwK_wordRows hK g5_gens g5_invs nWordV h2.1
  change v2N (frApply (frTable (mulRows (mulRows (QT2A.wR nWordU)
    (QT.etaRows (QT.uTab (locMats ()) (locInvs ())) 11 nMask)) (QT2A.wR nWordV))) p) = _
  rw [vec_mulRows (wf_mulRows hU hE) hV hp, vec_mulRows hU hE hp]
  change v2N (frApply (frTable (wordRows (QT2A.g5Mats ()) (QT2A.g5Invs ()) nWordV)) _) = _
  rw [h3, h2.2]
  change vwK rm one G5L G5iL nWordV (vecEtaK rm UL nMask
    (v2N (frApply (frTable (wordRows (QT2A.g5Mats ()) (QT2A.g5Invs ()) nWordU)) p))) = _
  rw [h1]
  rfl

theorem nElt_fix_of {p : V2} (hp : p.wf = true) (h : nVec (v2N p) = v2N p) :
    nElt • toRow p.toVec = toRow p.toVec := by
  have e := v2N_inj ((nVec_spec hp).trans h)
  have e2 : nElt⁻¹ • toRow p.toVec = toRow p.toVec := by
    rw [← ofRow_inj, inv_smul_row, ← QT.Mx_apply, Mx_nElt hM5]
    change Matrix.vecMul p.toVec (CFSG.Sporadic.J4.rowsMatrix nRows) = p.toVec
    rw [← frApply_toVec_eq_vecMul, e]
  rw [← e2, smul_inv_smul, e2]

theorem n_fix_pts {i : ℕ} (hi : i < 14) (h : nVec (getN 0 XPTS i) = getN 0 XPTS i) :
    nElt • ptsV i = ptsV i :=
  nElt_fix_of (pV_wf hi) (by rw [v2N_pV hi]; exact h)

theorem nElt_fix_v : nElt • v = v := by
  rw [← ptsV_zero]
  exact n_fix_pts (by norm_num) (Nat.eq_of_beq_eq_true n_fix_root)

theorem nElt_fix_qA : nElt • qA = qA :=
  n_fix_pts (by norm_num) (Nat.eq_of_beq_eq_true n_fix_qA)

theorem nElt_fix_q1 : nElt • q1Row = q1Row := by
  have h := nElt_fix_of (p := x0Q1) (by decide) (Nat.eq_of_beq_eq_true n_fix_q1)
  exact h

theorem nElt_conj' :
    nElt * fiveElt * nElt⁻¹ = fiveElt ^ 2 := by
  rw [mul_inv_eq_iff_eq_mul, nElt_conj hM5]

theorem qA_eq : qA = toRow (toVecD 112 QAN) := by
  rw [qA, ptsV_eq (by norm_num), Nat.eq_of_beq_eq_true qan_eq]

section Orbits

theorem qA_mem : qA ∈ orbit J v := by
  obtain ⟨g, -, hg⟩ := exists_of_mem_pts hM5 qA_mem_pts
  refine ⟨g, ?_⟩
  change g • v = _
  rw [v_eq_root]
  exact hg

end Orbits

noncomputable abbrev S0 : Subgroup J := X0Sub ⊓ stabilizer J v

noncomputable abbrev S1 : Subgroup J := S0 ⊓ stabilizer J q1Row

theorem card_S0 : Nat.card S0 = 480 := by
  have h := card_X0Sub_stabilizer hM5
  have hsub : S0.subgroupOf X0Sub = stabilizer X0Sub w₀ := by
    ext ⟨g, hg⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_stabilizer_iff]
    constructor
    · rintro ⟨-, h⟩
      change g • w₀ = w₀
      rw [show w₀ = v from v_eq_root.symm]
      exact h
    · intro h
      refine ⟨hg, ?_⟩
      have h' : g • w₀ = w₀ := h
      rw [show w₀ = v from v_eq_root.symm] at h'
      exact h'
  rw [← hsub] at h
  rw [← h]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : S0 ≤ X0Sub)).toEquiv).symm

theorem S0_fix_qA {g : J} (hg : g ∈ S0) : g • qA = qA :=
  S_fix_qA (Subgroup.mem_inf.1 hg).1 (Subgroup.mem_inf.1 hg).2

section Bound

theorem five_sizes : ∀ s ∈ L7, 5 ∣ 501397585920 / s → s = 1 ∨ s = 28336 ∨ s = 32643072 := by
  decide +kernel

end Bound

end CertificateChecks.KernelJ4Count.Five

end
