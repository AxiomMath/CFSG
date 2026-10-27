module

public import Certificates.Kernel.Sporadic.SuzK.Light
public import CFSG.Certificates.Kernel.Spor.F3LaneSepSound
public import CFSG.Certificates.Kernel.Spor.Mat3Sound
public import CFSG.Sporadic.Suz.W64Spec
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.F3.Native CFSG.KS CFSG.KS.F3L CFSG.KS.F3R CFSG.KS.Mat3 CFSG.KC.Enum CFSG.KC.Ord
  CFSG.Sporadic.Suz.Native

theorem eqF_iff {X Y : V} : eqF X Y = true ↔ X = Y := by
  unfold eqF
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact V.ext' h1 h2
  · rintro rfl
    exact ⟨rfl, rfl⟩

structure Canon (X : V) : Prop where
  wf : X.wf = true
  p : X.p < 2 ^ (64 * 64)
  m : X.m < 2 ^ (64 * 64)

set_option exponentiation.threshold 6000 in
theorem canonF_spec {X : V} (h : canonF X = true) : Canon X := by
  unfold canonF at h
  rw [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
    Nat.beq_eq, Nat.blt_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e : Nat.shiftLeft 1 4096 = 2 ^ (64 * 64) := Nat.one_shiftLeft (64 * 64)
  refine ⟨?_, lt_of_lt_of_eq h2 e, lt_of_lt_of_eq h3 e⟩
  unfold V.wf
  rw [beq_iff_eq]
  exact h1

theorem canons : Canon (ln 0) ∧ Canon (ln 1) ∧ Canon (ln 2) ∧ Canon (ln 3) ∧ Canon (ln 4) ∧
    Canon (ln 5) ∧ Canon (ln 6) ∧ Canon (ln 7) ∧ Canon (ln 8) ∧ Canon (mulF (ln 0) (ln 1)) := by
  have h := canon_ok
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨canonF_spec h0, canonF_spec h1, canonF_spec h2, canonF_spec h3, canonF_spec h4,
    canonF_spec h5, canonF_spec h6, canonF_spec h7, canonF_spec h8, canonF_spec h9⟩

theorem matA_eq : matA = unlane 64 (ln 0) := by
  unfold matA
  rw [SeedA.eq]
  exact rowsOf_seed seedA_ok

theorem matB_eq : matB = unlane 64 (ln 1) := by
  unfold matB
  rw [SeedB.eq]
  exact rowsOf_seed seedB_ok

theorem lit_eq {X : Array V} {L : V} (hL : Canon L) (hX : canonM 64 X = true)
    (h : eqMK 64 X (unlane 64 L) = true) : X = unlane 64 L := by
  have h' : eqM 64 X (unlane 64 L) = true := by rw [eqM_eq]; exact h
  exact eq_of_canonM hX (canonM_unlane 64 hL.wf) (toMat_eq_of_eqM h')

theorem idM_eq : idM 64 = unlane 64 (ln 3) := lit_eq canons.2.2.2.1 (canonM_idM 64) id_ok

theorem canonLits : canonM 64 (formF ()) = true ∧ canonM 64 (formP ()) = true ∧
    canonM 64 (formPinv ()) = true ∧ canonM 64 diagDK = true ∧ canonM 64 (rootRows ()) = true := by
  have h := canonLit_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [canonM_eq]
  exact ⟨h1, h2, h3, h4, h5⟩

theorem diagD_eqK : diagD () = diagDK := by
  unfold diagD diagDK
  simp only [ofFn_eq]

theorem formF_eq : formF () = unlane 64 (ln 4) :=
  lit_eq canons.2.2.2.2.1 canonLits.1 formF_ok
theorem formP_eq : formP () = unlane 64 (ln 5) :=
  lit_eq canons.2.2.2.2.2.1 canonLits.2.1 formP_ok
theorem formPinv_eq : formPinv () = unlane 64 (ln 6) :=
  lit_eq canons.2.2.2.2.2.2.1 canonLits.2.2.1 formPinv_ok
theorem diagD_eq : diagD () = unlane 64 (ln 7) := by
  rw [diagD_eqK]
  exact lit_eq canons.2.2.2.2.2.2.2.1 canonLits.2.2.2.1 diagD_ok
theorem rootRows_eq : rootRows () = unlane 64 (ln 8) :=
  lit_eq canons.2.2.2.2.2.2.2.2.1 canonLits.2.2.2.2 rootL_ok

theorem mul_eq' (X Y : V) : mul 64 (unlane 64 X) (unlane 64 Y) = unlane 64 (mulF X Y) :=
  mul_unlane (by norm_num) X Y

theorem powM_eq' (X : V) (e : Nat) : powM 64 (unlane 64 X) e = unlane 64 (powF X e) :=
  powM_unlane (by norm_num) idM_eq X e

theorem unlane_size' (X : V) : (unlane 64 X).size = 64 := unlane_size 64 X

theorem ne_of_lane {X Y : V} (hX : Canon X) (hY : Canon Y) (h : X ≠ Y) :
    eqM 64 (unlane 64 X) (unlane 64 Y) = false := by
  cases e : eqM 64 (unlane 64 X) (unlane 64 Y)
  · rfl
  · exact absurd (eqM_unlane hX.wf hY.wf hX.p hX.m hY.p hY.m e) h

theorem matrix_ok : matrixChecks () = true := by
  obtain ⟨cA, cB, -, cI, -, -, -, -, -, cAB⟩ := canons
  have hne := ne_ok
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hne
  obtain ⟨n1, n2, n3⟩ := hne
  rw [Bool.not_eq_true', ← Bool.not_eq_true, eqF_iff] at n1 n2 n3
  unfold matrixChecks
  rw [matA_eq, matB_eq, idM_eq, mul_eq', mul_eq', powM_eq', powM_eq',
    eqF_iff.1 a2_ok, eqF_iff.1 b3_ok, eqF_iff.1 ab13_ok,
    canonM_unlane 64 cA.wf, canonM_unlane 64 cB.wf, canonM_unlane 64 cI.wf,
    canonM_unlane 64 cAB.wf, eqM_self (unlane_size' _), ne_of_lane cA cI n1, ne_of_lane cB cI n2,
    ne_of_lane cAB cI n3]
  rfl

theorem transpose_eq' {X : V} (h : Canon X) : transpose 64 (unlane 64 X) = unlane 64 (trLane 64 X) :=
  transpose_unlane h.wf

theorem form_ok : formChecks () = true := by
  obtain ⟨cA, cB, -, cI, cF, cP, cPi, cD, -, -⟩ := canons
  have hw := wfLit_ok
  simp only [Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨w1, w2⟩, w3⟩, s1⟩, s2⟩, s3⟩ := hw
  unfold formChecks
  rw [wfM_eq, wfM_eq, wfM_eq, w1, w2, w3, s1, s2, s3, matA_eq, matB_eq, formF_eq, formP_eq,
    formPinv_eq, diagD_eq, idM_eq, transpose_eq' cA, transpose_eq' cB, transpose_eq' cP, mul_eq',
    mul_eq', mul_eq', mul_eq', mul_eq', mul_eq', mul_eq', eqF_iff.1 fA_ok, eqF_iff.1 fB_ok,
    eqF_iff.1 fP_ok, eqF_iff.1 fPi_ok, eqM_self (unlane_size' (ln 4)),
    eqM_self (unlane_size' (ln 7)), eqM_self (unlane_size' (ln 3))]
  rfl

theorem pow4096 : (2 : Nat) ^ 4096 - 1 = mask 4096 := by
  rw [CFSG.KS.Raw.Orb.mask_eq']

theorem lane_p_bit (X t : Nat) : (⟨X &&& (2 ^ 4096 - 1), X >>> 4096⟩ : V).p.testBit t =
    (decide (t < 4096) && X.testBit t) := lo_bit

theorem toMat_lane3 (X : Nat) :
    toMat 64 (unlane 64 ⟨X &&& (2 ^ 4096 - 1), X >>> 4096⟩) = mat3 64 4096 X := by
  ext i j
  rw [toMat_apply, unlane_get _ i.isLt, V.val_eq_bitVal, blk_p, blk_m]
  change bitVal (decide (j.val < 64) && (X &&& (2 ^ 4096 - 1)).testBit (64 * i.val + j.val))
    (decide (j.val < 64) && (X >>> 4096).testBit (64 * i.val + j.val)) = _
  rw [lo_bit, Nat.testBit_shiftRight]
  have hij : 64 * i.val + j.val < 4096 := by
    have := i.isLt
    have := j.isLt
    omega
  simp only [decide_eq_true j.isLt, decide_eq_true hij, Bool.true_and]
  rfl

theorem laneK_eq (k : Nat) : laneK k = ⟨kx k &&& (2 ^ 4096 - 1), kx k >>> 4096⟩ := by
  unfold laneK
  rw [strictT_eq, ← CFSG.KS.Raw.Orb.mask_eq' 4096]
  rfl

theorem mat3_kx (k : Nat) : mat3 64 4096 (kx k) = toMat 64 (unlane 64 (laneK k)) := by
  rw [laneK_eq, toMat_lane3]

theorem x3_lane {i : Nat} (h : Canon (ln i)) : ln i = ⟨x3 i &&& (2 ^ 4096 - 1), x3 i >>> 4096⟩ := by
  have hp : (ln i).p < 2 ^ 4096 := h.p
  have hp' : lt (2 * i) < 2 ^ 4096 := hp
  have e : x3 i = lt (2 * i) + 2 ^ 4096 * lt (2 * i + 1) := by
    unfold x3
    change lt (2 * i) + lt (2 * i + 1) <<< 4096 = _
    rw [Nat.shiftLeft_eq]
    ring
  apply V.ext'
  · change (ln i).p = x3 i &&& (2 ^ 4096 - 1)
    rw [Nat.and_two_pow_sub_one_eq_mod, e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp']
    rfl
  · change (ln i).m = x3 i >>> 4096
    rw [Nat.shiftRight_eq_div_pow, e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hp', Nat.zero_add]
    rfl

theorem mat3_x3 {i : Nat} (h : Canon (ln i)) : mat3 64 4096 (x3 i) = toMat 64 (unlane 64 (ln i)) := by
  rw [x3_lane h, toMat_lane3]

theorem mem_unlane_lt {L v : V} (hv : v ∈ unlane 64 L) : v.p < 2 ^ 64 ∧ v.m < 2 ^ 64 := by
  unfold unlane at hv
  rw [Array.mem_ofFn] at hv
  obtain ⟨i, rfl⟩ := hv
  exact ⟨blk_p_lt 64 L i.val, blk_m_lt 64 L i.val⟩

theorem toVM_ofV_unlane (L : V) : toVM ((unlane 64 L).map ofV) = unlane 64 L :=
  toVM_map_ofV fun _ hv => mem_unlane_lt hv

theorem wA_eq : wA () = (unlane 64 (ln 0)).map ofV := by
  unfold wA
  rw [matA_eq]

theorem wB_eq : wB () = (unlane 64 (ln 1)).map ofV := by
  unfold wB
  rw [matB_eq]

theorem toVM_wA : toVM (wA ()) = unlane 64 (ln 0) := by rw [wA_eq, toVM_ofV_unlane]
theorem toVM_wB : toVM (wB ()) = unlane 64 (ln 1) := by rw [wB_eq, toVM_ofV_unlane]
theorem toVM_wBi : toVM (wBi ()) = unlane 64 (ln 2) := by
  unfold wBi
  rw [toVM_mulW, toVM_wB, mul_eq', eqF_iff.1 b2_ok]

theorem wRoot_eq : wRoot () = (unlane 64 (ln 8)).map ofV := by
  unfold wRoot
  rw [rootRows_eq]

noncomputable abbrev ML (i : Nat) : Matrix (Fin 64) (Fin 64) (ZMod 3) := toMat 64 (unlane 64 (ln i))

theorem rowsWF_ln {i : Nat} (h : Canon (ln i)) : RowsWF (unlane 64 (ln i)) :=
  RowsWF.of_canonM (canonM_unlane 64 h.wf)

theorem ML_mul {i j : Nat} (hi : Canon (ln i)) (hj : Canon (ln j)) :
    ML i * ML j = toMat 64 (unlane 64 (mulF (ln i) (ln j))) := by
  rw [← mul_eq', toMat_mul (unlane_size' _) (rowsWF_ln hi) (rowsWF_ln hj)]

theorem ML3 : ML 3 = 1 := by
  change toMat 64 (unlane 64 (ln 3)) = 1
  rw [← idM_eq, toMat_idM]

theorem A_sq : ML 0 * ML 0 = 1 := by
  rw [ML_mul canons.1 canons.1, eqF_iff.1 a2_ok]
  exact ML3

theorem B_B2 : ML 1 * ML 2 = 1 := by
  rw [ML_mul canons.2.1 canons.2.2.1, eqF_iff.1 bb2_ok]
  exact ML3

theorem B2_eq : ML 2 = ML 1 * ML 1 := by
  rw [ML_mul canons.2.1 canons.2.1, eqF_iff.1 b2_ok]

theorem B2_B : ML 2 * ML 1 = 1 := by
  rw [B2_eq, mul_assoc, ← B2_eq, B_B2]

theorem toMat_matA : toMat 64 matA = ML 0 := by rw [matA_eq]
theorem toMat_matB : toMat 64 matB = ML 1 := by rw [matB_eq]

end CertificateChecks.KernelSpor.SuzK

end
