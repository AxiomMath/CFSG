module

public import Certificates.Kernel.Fi22Nine.Sound
public import Certificates.Kernel.Fi22Nine.Chk

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Fi22Nine

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CertificateChecks.KernelSpor
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.Certificates.Native
open CertificateChecks.KernelSpor.Fi22F2 (gI bT)
open CFSG.Certificates (finSet)
open scoped Pointwise

@[expose] noncomputable def cP (j : Nat) : Equiv.Perm (Fin 3510) := fi22CentPerm (19 + j)

@[expose] noncomputable def xE : Equiv.Perm (Fin 3510) := wP cP 0 51
@[expose] noncomputable def yE : Equiv.Perm (Fin 3510) := wP cP 1 37
@[expose] noncomputable def aE : Equiv.Perm (Fin 3510) := wP cP 2 67
@[expose] noncomputable def hE : Equiv.Perm (Fin 3510) := wP cP 3 58
@[expose] noncomputable def h1E : Equiv.Perm (Fin 3510) := wP cP 4 74
@[expose] noncomputable def gE : Equiv.Perm (Fin 3510) := wP fi22GenPerm 5 1805
@[expose] noncomputable def pE : Equiv.Perm (Fin 3510) := wP fi22GenPerm 6 353
@[expose] noncomputable def sE : Equiv.Perm (Fin 3510) := fi22U * pE * hE
@[expose] noncomputable def s1E : Equiv.Perm (Fin 3510) := fi22U * pE * h1E

theorem let_parts : (∀ k < 51, wL 0 k < 9) ∧ (∀ k < 37, wL 1 k < 9) ∧ (∀ k < 67, wL 2 k < 9) ∧
    (∀ k < 58, wL 3 k < 9) ∧ (∀ k < 74, wL 4 k < 9) ∧ (∀ k < 1805, wL 5 k < 2) ∧
    ∀ k < 353, wL 6 k < 2 := by
  have h := lett
  unfold letK at h
  simp only [bAnd_iff] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨letB_spec h0, letB_spec h1, letB_spec h2, letB_spec h3, letB_spec h4, letB_spec h5,
    letB_spec h6⟩

theorem elem_parts :
    eqB (fun b => xW (xW (xW b))) (fun b => b) = true ∧
    eqB (fun b => yW (yW (yW b))) (fun b => b) = true ∧
    eqB (fun b => aW (aW (aW b))) (fun b => b) = true ∧
    eqB (fun b => xW (yW b)) (fun b => yW (xW b)) = true ∧
    Bool.not (eqB xW (fun b => b)) = true ∧ Bool.not (eqB yW (fun b => b)) = true ∧
    Bool.not (eqB yW xW) = true ∧ Bool.not (eqB yW (fun b => xW (xW b))) = true ∧
    Bool.not (eqB aW (fun b => b)) = true ∧
    eqB (fun b => aW (gW (aW b))) gW = true ∧
    eqB (fun b => pW (hW (zO b))) (fun b => uO (zO (uO (pW (hW b))))) = true ∧
    eqB (fun b => pW (h1W (zO b))) (fun b => uO (zO (uO (pW (h1W b))))) = true ∧
    fixL X0 6 xW = true ∧ fixL X0 6 yW = true ∧ fixL X1 18 aW = true ∧
    fixL X0 6 (fun q => uO (pW (hW q))) = true ∧
    fixL X0 6 (fun q => uO (pW (h1W q))) = true ∧ fixL X1 18 (fun q => uO (pW (h1W q))) = true ∧
    allN 9 (fun s => bAnd(fixL X0 6 (tS s), fixL X1 18 (tS s))) = true ∧
    Nat.blt zI 131072 = true ∧
    allN 3510 (fun q => Nat.beq (zO q) (Fi22F2.gI zI q)) = true ∧
    centB zI = true ∧ Bool.not (eqB zO (fun b => b)) = true := by
  have h := elem
  unfold elemK at h
  simp only [bAnd_iff] at h
  exact h

section Facts

theorem cG_eq' : ∀ j < 9, ∀ y : Fin 3510, cG j y = (cP j y : Nat) := by
  intro j hj y
  rw [cP.eq_1 j]
  exact cG_eq hj y

theorem pG_eq' : ∀ j < 2, ∀ y : Fin 3510, pG j y = (fi22GenPerm j y : Nat) :=
  fun _ hj y => pG_eq hj y

theorem xW_eq (y : Fin 3510) : xW y = (xE y : Nat) := by
  rw [xW.eq_1, xE.eq_1]
  exact walk_eq (B := 9) cG_eq' 51 let_parts.1 y
theorem yW_eq (y : Fin 3510) : yW y = (yE y : Nat) := by
  rw [yW.eq_1, yE.eq_1]
  exact walk_eq (B := 9) cG_eq' 37 let_parts.2.1 y
theorem aW_eq (y : Fin 3510) : aW y = (aE y : Nat) := by
  rw [aW.eq_1, aE.eq_1]
  exact walk_eq (B := 9) cG_eq' 67 let_parts.2.2.1 y
theorem hW_eq (y : Fin 3510) : hW y = (hE y : Nat) := by
  rw [hW.eq_1, hE.eq_1]
  exact walk_eq (B := 9) cG_eq' 58 let_parts.2.2.2.1 y
theorem h1W_eq (y : Fin 3510) : h1W y = (h1E y : Nat) := by
  rw [h1W.eq_1, h1E.eq_1]
  exact walk_eq (B := 9) cG_eq' 74 let_parts.2.2.2.2.1 y
theorem gW_eq (y : Fin 3510) : gW y = (gE y : Nat) := by
  rw [gW.eq_1, gE.eq_1]
  exact walk_eq (B := 2) pG_eq' 1805 let_parts.2.2.2.2.2.1 y
theorem pW_eq (y : Fin 3510) : pW y = (pE y : Nat) := by
  rw [pW.eq_1, pE.eq_1]
  exact walk_eq (B := 2) pG_eq' 353 let_parts.2.2.2.2.2.2 y

theorem ev_comp {f f' : Nat → Nat} {X Y : Equiv.Perm (Fin 3510)}
    (hf : ∀ y : Fin 3510, f y = (X y : Nat)) (hf' : ∀ y : Fin 3510, f' y = (Y y : Nat)) :
    ∀ y : Fin 3510, f (f' y) = ((X * Y) y : Nat) := fun y => by
  rw [hf' y, hf (Y y), Equiv.Perm.mul_apply]

theorem ev_id : ∀ y : Fin 3510, (fun b : Nat => b) y = ((1 : Equiv.Perm (Fin 3510)) y : Nat) :=
  fun _ => rfl

theorem C_le_P : fi22H 1 ≤ fi22P := fun _ h => (fi22H_le (c := 1) (by norm_num) h).1

theorem cP_mem : ∀ j < 9, cP j ∈ fi22H 1 := by
  intro j hj
  rw [cP.eq_1 j]
  exact cPerm_mem hj

theorem pP_mem : ∀ j < 2, fi22GenPerm j ∈ fi22P := fun _ hj => pPerm_mem hj

theorem xE_mem : xE ∈ fi22H 1 := by
  rw [xE.eq_1]
  exact wP_mem (B := 9) cP_mem 51 let_parts.1
theorem yE_mem : yE ∈ fi22H 1 := by
  rw [yE.eq_1]
  exact wP_mem (B := 9) cP_mem 37 let_parts.2.1
theorem aE_mem : aE ∈ fi22H 1 := by
  rw [aE.eq_1]
  exact wP_mem (B := 9) cP_mem 67 let_parts.2.2.1
theorem hE_mem : hE ∈ fi22H 1 := by
  rw [hE.eq_1]
  exact wP_mem (B := 9) cP_mem 58 let_parts.2.2.2.1
theorem h1E_mem : h1E ∈ fi22H 1 := by
  rw [h1E.eq_1]
  exact wP_mem (B := 9) cP_mem 74 let_parts.2.2.2.2.1
theorem gE_mem : gE ∈ fi22P := by
  rw [gE.eq_1]
  exact wP_mem (B := 2) pP_mem 1805 let_parts.2.2.2.2.2.1
theorem pE_mem : pE ∈ fi22P := by
  rw [pE.eq_1]
  exact wP_mem (B := 2) pP_mem 353 let_parts.2.2.2.2.2.2

theorem z_eq : fi22ExtRep 1 = fi22TProd (Fi22C3151.xF zI) := by
  have hz := elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hI := n9Blt elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  ext y
  have e := Nat.eq_of_beq_eq_true (allN_spec hz y y.2)
  rw [← zO_eq y, e, gI_eq hI y]

theorem z_mem_T : fi22ExtRep 1 ∈ fi22OuterT := by
  rw [z_eq]
  exact fi22TProd_mem _

theorem z_mem_P : fi22ExtRep 1 ∈ fi22P := fi22OuterT_le z_mem_T

theorem z_ne_one : fi22ExtRep 1 ≠ 1 :=
  ne_of_eqB zO_eq ev_id elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem z_comm_seed {s : Nat} (hs : s < 9) : fi22ExtRep 1 * fi22TSeed s = fi22TSeed s * fi22ExtRep 1 := by
  have hc := allN_spec elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s hs
  have hI := n9Blt elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine sepB (fi22P.mul_mem z_mem_P (fi22OuterT_le (tSeed_mem hs)))
    (fi22P.mul_mem (fi22OuterT_le (tSeed_mem hs)) z_mem_P) fun t ht => ?_
  have h := Nat.eq_of_beq_eq_true (allN_spec hc t ht)
  have hz : ∀ y : Fin 3510, Fi22F2.gI zI y = (fi22ExtRep 1 y : Nat) := fun y => by
    rw [gI_eq hI y, z_eq]
  have e1 := ev_comp hz (tS_eq hs) ⟨bT t, n9BT ht⟩
  have e2 := ev_comp (tS_eq hs) hz ⟨bT t, n9BT ht⟩
  exact e1.symm.trans (h.trans e2)

theorem z_central : ∀ y ∈ fi22OuterT, fi22ExtRep 1 * y = y * fi22ExtRep 1 := by
  have hle : fi22OuterT ≤ Subgroup.centralizer ({fi22ExtRep 1} : Set (Equiv.Perm (Fin 3510))) := by
    rw [fi22OuterT_eq_closure, Subgroup.closure_le]
    rintro g ⟨s, hs, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (z_comm_seed hs).symm
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem center_mem {t : Equiv.Perm (Fin 3510)} (ht : t ∈ fi22OuterT)
    (hc : ∀ y ∈ fi22OuterT, t * y = y * t) : t = 1 ∨ t = fi22ExtRep 1 :=
  center_eq ht hc z_mem_P

theorem cube_of_check {w : Equiv.Perm (Fin 3510)} (hw : w ∈ fi22H 1) {wN : Nat → Nat}
    (hwN : ∀ y : Fin 3510, wN y = (w y : Nat))
    (h : eqB (fun b => wN (wN (wN b))) (fun b => b) = true) : w ^ 3 = 1 := by
  have e2 : ∀ y : Fin 3510, wN (wN y) = ((w * w) y : Nat) := ev_comp hwN hwN
  have e3 : ∀ y : Fin 3510, wN (wN (wN y)) = ((w * (w * w)) y : Nat) :=
    ev_comp (f' := fun b => wN (wN b)) hwN e2
  have hP := C_le_P hw
  rw [pow_three]
  exact eqB_eq (f := fun b => wN (wN (wN b))) (f' := fun b => b) e3 ev_id
    (fi22P.mul_mem hP (fi22P.mul_mem hP hP)) fi22P.one_mem h

theorem x3 : xE ^ 3 = 1 := cube_of_check xE_mem xW_eq elem_parts.1

theorem y3 : yE ^ 3 = 1 := cube_of_check yE_mem yW_eq elem_parts.2.1

theorem a3 : aE ^ 3 = 1 := cube_of_check aE_mem aW_eq elem_parts.2.2.1

theorem xy_comm : Commute xE yE := by
  have e1 : ∀ y : Fin 3510, xW (yW y) = ((xE * yE) y : Nat) := ev_comp xW_eq yW_eq
  have e2 : ∀ y : Fin 3510, yW (xW y) = ((yE * xE) y : Nat) := ev_comp yW_eq xW_eq
  exact eqB_eq (f := fun b => xW (yW b)) (f' := fun b => yW (xW b)) e1 e2
    (fi22P.mul_mem (C_le_P xE_mem) (C_le_P yE_mem)) (fi22P.mul_mem (C_le_P yE_mem) (C_le_P xE_mem))
    elem_parts.2.2.2.1

theorem x_ne_one : xE ≠ 1 := ne_of_eqB (f' := fun b => b) xW_eq ev_id elem_parts.2.2.2.2.1

theorem y_ne_one : yE ≠ 1 := ne_of_eqB (f' := fun b => b) yW_eq ev_id elem_parts.2.2.2.2.2.1

theorem y_ne_x : yE ≠ xE := ne_of_eqB yW_eq xW_eq elem_parts.2.2.2.2.2.2.1

theorem y_ne_x2 : yE ≠ xE ^ 2 := by
  have e2 : ∀ y : Fin 3510, xW (xW y) = ((xE * xE) y : Nat) := ev_comp xW_eq xW_eq
  rw [pow_two]
  exact ne_of_eqB (f' := fun b => xW (xW b)) yW_eq e2 elem_parts.2.2.2.2.2.2.2.1

theorem a_ne_one : aE ≠ 1 := ne_of_eqB (f' := fun b => b) aW_eq ev_id elem_parts.2.2.2.2.2.2.2.2.1

theorem g_inv : gE * aE * gE⁻¹ = aE⁻¹ := by
  have e1 : ∀ y : Fin 3510, gW (aW y) = ((gE * aE) y : Nat) := ev_comp gW_eq aW_eq
  have e2 : ∀ y : Fin 3510, aW (gW (aW y)) = ((aE * (gE * aE)) y : Nat) :=
    ev_comp (f' := fun b => gW (aW b)) aW_eq e1
  have h : aE * (gE * aE) = gE := eqB_eq (f := fun b => aW (gW (aW b))) (f' := gW) e2 gW_eq
    (fi22P.mul_mem (C_le_P aE_mem) (fi22P.mul_mem gE_mem (C_le_P aE_mem))) gE_mem
    elem_parts.2.2.2.2.2.2.2.2.2.1
  calc gE * aE * gE⁻¹ = aE⁻¹ * (aE * (gE * aE)) * gE⁻¹ := by group
    _ = aE⁻¹ := by rw [h]; group

theorem u_conj_mem {g : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22P) : fi22U * g * fi22U ∈ fi22P := by
  have h := (Subgroup.mem_normalizer_iff.mp fi22U_mem_normalizer g).mp hg
  rwa [fi22U_inv] at h

theorem comm_of_check {w : Equiv.Perm (Fin 3510)} (hw : w ∈ fi22H 1) {wN : Nat → Nat}
    (hwN : ∀ y : Fin 3510, wN y = (w y : Nat))
    (h : eqB (fun b => pW (wN (zO b))) (fun b => uO (zO (uO (pW (wN b)))))  = true) :
    Commute (fi22U * pE * w) (fi22ExtRep 1) := by
  have hpw : pE * w ∈ fi22P := fi22P.mul_mem pE_mem (C_le_P hw)
  have e : pE * w * fi22ExtRep 1 = fi22U * fi22ExtRep 1 * fi22U * (pE * w) := by
    have a1 : ∀ y : Fin 3510, wN (zO y) = ((w * fi22ExtRep 1) y : Nat) := ev_comp hwN zO_eq
    have a2 : ∀ y : Fin 3510, pW (wN (zO y)) = ((pE * (w * fi22ExtRep 1)) y : Nat) :=
      ev_comp (f' := fun b => wN (zO b)) pW_eq a1
    have b1 : ∀ y : Fin 3510, pW (wN y) = ((pE * w) y : Nat) := ev_comp pW_eq hwN
    have b2 : ∀ y : Fin 3510, uO (pW (wN y)) = ((fi22U * (pE * w)) y : Nat) :=
      ev_comp (f' := fun b => pW (wN b)) uO_eq b1
    have b3 : ∀ y : Fin 3510, zO (uO (pW (wN y))) =
        ((fi22ExtRep 1 * (fi22U * (pE * w))) y : Nat) :=
      ev_comp (f' := fun b => uO (pW (wN b))) zO_eq b2
    have b4 : ∀ y : Fin 3510, uO (zO (uO (pW (wN y)))) =
        ((fi22U * (fi22ExtRep 1 * (fi22U * (pE * w)))) y : Nat) :=
      ev_comp (f' := fun b => zO (uO (pW (wN b)))) uO_eq b3
    have hU : fi22U * (fi22ExtRep 1 * (fi22U * (pE * w))) ∈ fi22P := by
      have := fi22P.mul_mem (u_conj_mem z_mem_P) hpw
      simpa only [mul_assoc] using this
    have h' := eqB_eq (f := fun b => pW (wN (zO b))) (f' := fun b => uO (zO (uO (pW (wN b)))))
      a2 b4 (fi22P.mul_mem pE_mem (fi22P.mul_mem (C_le_P hw) z_mem_P)) hU h
    simpa only [mul_assoc] using h'
  have hu := fi22U_mul_self
  change fi22U * pE * w * fi22ExtRep 1 = fi22ExtRep 1 * (fi22U * pE * w)
  calc fi22U * pE * w * fi22ExtRep 1 = fi22U * (pE * w * fi22ExtRep 1) := by group
    _ = fi22U * (fi22U * fi22ExtRep 1 * fi22U * (pE * w)) := by rw [e]
    _ = (fi22U * fi22U) * fi22ExtRep 1 * (fi22U * pE * w) := by group
    _ = fi22ExtRep 1 * (fi22U * pE * w) := by rw [hu, one_mul]

theorem s_comm : Commute sE (fi22ExtRep 1) := by
  rw [sE.eq_1]
  exact comm_of_check hE_mem hW_eq elem_parts.2.2.2.2.2.2.2.2.2.2.1

theorem s1_comm : Commute s1E (fi22ExtRep 1) := by
  rw [s1E.eq_1]
  exact comm_of_check h1E_mem h1W_eq elem_parts.2.2.2.2.2.2.2.2.2.2.2.1

theorem us_mem : fi22U * sE ∈ fi22P := by
  have e : fi22U * sE = pE * hE := by
    rw [sE, ← mul_assoc, ← mul_assoc, fi22U_mul_self, one_mul]
  rw [e]
  exact fi22P.mul_mem pE_mem (C_le_P hE_mem)

theorem us1_mem : fi22U * s1E ∈ fi22P := by
  have e : fi22U * s1E = pE * h1E := by
    rw [s1E, ← mul_assoc, ← mul_assoc, fi22U_mul_self, one_mul]
  rw [e]
  exact fi22P.mul_mem pE_mem (C_le_P h1E_mem)

theorem x_fix : xE • finSet 3510 X0 = finSet 3510 X0 :=
  smul_finSet_eq rfl xW_eq elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem y_fix : yE • finSet 3510 X0 = finSet 3510 X0 :=
  smul_finSet_eq rfl yW_eq elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem a_fix : aE • finSet 3510 X1 = finSet 3510 X1 :=
  smul_finSet_eq rfl aW_eq elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem up_eq : ∀ y : Fin 3510, uO (pW y) = ((fi22U * pE) y : Nat) := ev_comp uO_eq pW_eq

theorem sW_eq : ∀ y : Fin 3510, uO (pW (hW y)) = ((fi22U * pE * hE) y : Nat) :=
  ev_comp (f := fun b => uO (pW b)) up_eq hW_eq

theorem s1W_eq : ∀ y : Fin 3510, uO (pW (h1W y)) = ((fi22U * pE * h1E) y : Nat) :=
  ev_comp (f := fun b => uO (pW b)) up_eq h1W_eq

theorem s_fix : sE • finSet 3510 X0 = finSet 3510 X0 := by
  rw [sE.eq_1]
  exact smul_finSet_eq (f := fun q => uO (pW (hW q))) rfl sW_eq
    elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s1_fix : s1E • finSet 3510 X1 = finSet 3510 X1 := by
  rw [s1E.eq_1]
  exact smul_finSet_eq (f := fun q => uO (pW (h1W q))) rfl s1W_eq
    elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem seed_fix {s : Nat} (hs : s < 9) :
    fi22TSeed s • finSet 3510 X0 = finSet 3510 X0 ∧
      fi22TSeed s • finSet 3510 X1 = finSet 3510 X1 := by
  obtain ⟨h0, h1⟩ := n9And (allN_spec elem_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s hs)
  exact ⟨smul_finSet_eq rfl (tS_eq hs) h0, smul_finSet_eq rfl (tS_eq hs) h1⟩

theorem T_fix0 : fi22OuterT ≤ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (finSet 3510 X0) := by
  rw [fi22OuterT_eq_closure, Subgroup.closure_le]
  rintro g ⟨s, hs, rfl⟩
  exact (seed_fix hs).1

theorem T_fix1 : fi22OuterT ≤ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (finSet 3510 X1) := by
  rw [fi22OuterT_eq_closure, Subgroup.closure_le]
  rintro g ⟨s, hs, rfl⟩
  exact (seed_fix hs).2

theorem orb_parts : (∀ k < 45, rowO 0 6 45 X0 k = true) ∧ oF 0 5 0 < 45 ∧
    (∀ k < 135, rowO 1 18 135 X1 k = true) ∧ oF 1 5 0 < 135 := by
  have h := orb
  unfold orbK at h
  simp only [bAnd_iff] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨allN_spec h2, n9Blt h0, allN_spec h3, n9Blt h1⟩

theorem orb0_lower : 45 ≤ (Set.range fun g : ↥(fi22H 1) => g • finSet 3510 X0).ncard :=
  orb_lower (o := 0) (m := 6) (by norm_num) rfl orb_parts.1 orb_parts.2.1

theorem orb1_lower : 135 ≤ (Set.range fun g : ↥(fi22H 1) => g • finSet 3510 X1).ncard :=
  orb_lower (o := 1) (m := 18) (by norm_num) rfl orb_parts.2.2.1 orb_parts.2.2.2

theorem orb0_unique (horb : (Set.range fun g : ↥(fi22H 1) => g • finSet 3510 X0).ncard = 45) :
    ∀ y ∈ Set.range (fun g : ↥(fi22H 1) => g • finSet 3510 X0),
      (∀ t ∈ fi22OuterT, t • y = y) → y = finSet 3510 X0 :=
  orb_unique (o := 0) (m := 6) (by norm_num) rfl orb_parts.1 orb_parts.2.1 horb

theorem orb1_unique (horb : (Set.range fun g : ↥(fi22H 1) => g • finSet 3510 X1).ncard = 135) :
    ∀ y ∈ Set.range (fun g : ↥(fi22H 1) => g • finSet 3510 X1),
      (∀ t ∈ fi22OuterT, t • y = y) → y = finSet 3510 X1 :=
  orb_unique (o := 1) (m := 18) (by norm_num) rfl orb_parts.2.2.1 orb_parts.2.2.2 horb

end Facts

end CertificateChecks.KernelSpor.Fi22Nine

end
