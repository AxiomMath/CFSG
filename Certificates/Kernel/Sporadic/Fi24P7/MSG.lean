module

public import Certificates.Kernel.Sporadic.Fi24P7.Mat
import CFSG.Certificates.Kernel.Spor.Mat3Sound

public section

namespace CertificateChecks.KernelFi24P7

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 CertificateChecks.KernelFi24Fix
  CertificateChecks.KernelFi24Orb CertificateChecks.KernelFi24G2e CertificateChecks.KernelFi24Ext
  CertificateChecks.KernelFi24F3d CFSG.KC.Loop CFSG.KD.Fi24G2e CFSG.KD.Fi24P7

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24G2e.BX CFSG.KD.Fi24Ext.MX CFSG.KD.BrFi24.MT
  CFSG.KD.Fi24Fix.MX CFSG.KD.Fi24P7.MX CFSG.KD.BrFi24.ONE CFSG.KD.BrFi24.MUL

theorem msg_lt12 : ∀ w ∈ [J.S0, J.S1, J.S2, J.S3, J.A0, J.B0, J.T2], ∀ g ∈ w, g < 12 := by
  decide +kernel

theorem msg_lt_app {u v : List ℕ} (hu : ∀ g ∈ u, g < 12) (hv : ∀ g ∈ v, g < 12) :
    ∀ g ∈ u ++ v, g < 12 := fun g hg => (List.mem_append.1 hg).elim (hu g) (hv g)

theorem beq_of_mt {X Y : ℕ} (hX : Cn X) (hY : Cn Y) (h : Mt X = Mt Y) : Nat.beq X Y = true := by
  rw [CFSG.KS.Mat3.mat3_inj (d := 781) (N := 609961) (by norm_num) hX hY h]
  exact Nat.beq_refl Y

theorem xw_word {w : List ℕ} (hw : ∀ g ∈ w, g < 12) :
    Cn (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w CFSG.KD.BrFi24.ONE) ∧
      ((xw w : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
        Mt (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w CFSG.KD.BrFi24.ONE) :=
  xw_mat hw (Nat.beq_refl _)

theorem pow3_word {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {G : ℕ}
    (hG : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w CFSG.KD.BrFi24.ONE) G = true)
    (h3 : Nat.beq (pow3 G) CFSG.KD.BrFi24.ONE = true) :
    Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (w ++ w ++ w) CFSG.KD.BrFi24.ONE)
      CFSG.KD.BrFi24.ONE = true := by
  obtain ⟨cG, vG⟩ := xw_mat hw hG
  have e3 : xw w ^ 3 = 1 := pow3_of_mat cG vG h3
  obtain ⟨c, v⟩ := xw_word (msg_lt_app (msg_lt_app hw hw) hw)
  refine beq_of_mt c cn_one ?_
  have e : xw w * xw w * xw w = 1 := by
    rw [← e3]
    simp only [pow_succ, pow_zero, one_mul]
  rw [← v, mt_one, xw_append, xw_append, e, Units.val_one]

theorem mt_pow7_pieces {G Q2 Q4 : ℕ} (cG : Cn G)
    (h2 : Nat.beq (CFSG.KD.BrFi24.MUL G G) Q2 = true)
    (h4 : Nat.beq (CFSG.KD.BrFi24.MUL Q2 Q2) Q4 = true)
    (h7 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL Q4 Q2) G) CFSG.KD.BrFi24.ONE = true) :
    Mt G ^ 7 = 1 := by
  obtain ⟨c2, e2⟩ := mul_mt cG cG
  rw [eq_of_beq' h2] at c2 e2
  obtain ⟨c4, e4⟩ := mul_mt c2 c2
  rw [eq_of_beq' h4] at c4 e4
  obtain ⟨c6, e6⟩ := mul_mt c4 c2
  obtain ⟨-, e7⟩ := mul_mt c6 cG
  rw [eq_of_beq' h7, mt_one, e6, e4, e2] at e7
  rw [e7]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem pow7_word {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {G Q2 Q4 : ℕ}
    (hG : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w CFSG.KD.BrFi24.ONE) G = true)
    (h2 : Nat.beq (CFSG.KD.BrFi24.MUL G G) Q2 = true)
    (h4 : Nat.beq (CFSG.KD.BrFi24.MUL Q2 Q2) Q4 = true)
    (h7 : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL Q4 Q2) G) CFSG.KD.BrFi24.ONE = true) :
    Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (w ++ w ++ w ++ w ++ w ++ w ++ w)
      CFSG.KD.BrFi24.ONE) CFSG.KD.BrFi24.ONE = true := by
  obtain ⟨cG, vG⟩ := xw_mat hw hG
  have e7 : xw w ^ 7 = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, vG, mt_pow7_pieces cG h2 h4 h7, Units.val_one]
  have hw7 : ∀ g ∈ w ++ w ++ w ++ w ++ w ++ w ++ w, g < 12 :=
    msg_lt_app (msg_lt_app (msg_lt_app (msg_lt_app (msg_lt_app (msg_lt_app hw hw) hw) hw) hw) hw) hw
  obtain ⟨c, v⟩ := xw_word hw7
  refine beq_of_mt c cn_one ?_
  have e : xw (w ++ w ++ w ++ w ++ w ++ w ++ w) = 1 := by
    simp only [xw_append]
    rw [← e7]
    simp only [pow_succ, pow_zero, one_mul]
  rw [← v, mt_one, e, Units.val_one]

theorem comm_word {u v : List ℕ} (hu : ∀ g ∈ u, g < 12) (hv : ∀ g ∈ v, g < 12) {Gu Gv : ℕ}
    (hGu : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG u CFSG.KD.BrFi24.ONE) Gu = true)
    (hGv : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG v CFSG.KD.BrFi24.ONE) Gv = true)
    (hc : Nat.beq (CFSG.KD.BrFi24.MUL Gu Gv) (CFSG.KD.BrFi24.MUL Gv Gu) = true) :
    Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (u ++ v) CFSG.KD.BrFi24.ONE)
      (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (v ++ u) CFSG.KD.BrFi24.ONE) = true := by
  obtain ⟨cu, vu⟩ := xw_mat hu hGu
  obtain ⟨cv, vv⟩ := xw_mat hv hGv
  obtain ⟨c1, v1⟩ := xw_word (msg_lt_app hu hv)
  obtain ⟨c2, v2⟩ := xw_word (msg_lt_app hv hu)
  refine beq_of_mt c1 c2 ?_
  obtain ⟨-, e1⟩ := mul_mt cu cv
  obtain ⟨-, e2⟩ := mul_mt cv cu
  rw [← v1, ← v2, xw_append, xw_append, Units.val_mul, Units.val_mul, vu, vv, ← e1, ← e2,
    eq_of_beq' hc]

theorem comm_mat {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {G X : ℕ} (cX : Cn X)
    (hG : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w CFSG.KD.BrFi24.ONE) G = true)
    (hc : Nat.beq (CFSG.KD.BrFi24.MUL G X) (CFSG.KD.BrFi24.MUL X G) = true) :
    Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w X)
      (CFSG.KD.BrFi24.MUL X (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w CFSG.KD.BrFi24.ONE)) =
      true := by
  rw [eq_of_beq' hG]
  obtain ⟨cG, vG⟩ := xw_mat hw hG
  obtain ⟨cL, vL⟩ := wordMul_τ cX w hw
  obtain ⟨cO, vO⟩ := wordMul_τ cn_one w hw
  rw [eq_of_beq' hG, mt_one, Matrix.mul_one] at vO
  obtain ⟨cR, vR⟩ := mul_mt cX cG
  refine beq_of_mt cL cR ?_
  obtain ⟨-, e1⟩ := mul_mt cG cX
  rw [vL, vR, ← vO, ← e1, eq_of_beq' hc, vR]

end CertificateChecks.KernelFi24P7

namespace CFSG.KD.Fi24P7

open CFSG.KC.Loop CFSG.KC.Fi24Fix CFSG.KD.Fi24G2e

theorem MS.s0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.S0 ++ J.S0 ++ J.S0) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true :=
  CertificateChecks.KernelFi24P7.pow3_word (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp))
    MSp.S0_val MSp.p3S0

theorem MS.s1 :Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.S1 ++ J.S1 ++ J.S1) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true :=
  CertificateChecks.KernelFi24P7.pow3_word (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp))
    MSp.S1_val MSp.p3S1

theorem MS.s2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.S2 ++ J.S2 ++ J.S2) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true :=
  CertificateChecks.KernelFi24P7.pow3_word (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp))
    MSp.S2_val MSp.p3S2

theorem MS.s3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.S3 ++ J.S3 ++ J.S3) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true :=
  CertificateChecks.KernelFi24P7.pow3_word (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp))
    MSp.S3_val MSp.p3S3

theorem MS.a0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG
    (J.A0 ++ J.A0 ++ J.A0 ++ J.A0 ++ J.A0 ++ J.A0 ++ J.A0) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true :=
  CertificateChecks.KernelFi24P7.pow7_word (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp))
    MSp.A0_val MSp.q2A0 MSp.q4A0 MSp.p7A0

theorem MS.b0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG
    (J.B0 ++ J.B0 ++ J.B0 ++ J.B0 ++ J.B0 ++ J.B0 ++ J.B0) CFSG.KD.BrFi24.ONE)
    CFSG.KD.BrFi24.ONE = true :=
  CertificateChecks.KernelFi24P7.pow7_word (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp))
    MSp.B0_val MSp.q2B0 MSp.q4B0 MSp.p7B0

theorem MS.a0s : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.A0 ++ J.S0) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (J.S0 ++ J.A0) CFSG.KD.BrFi24.ONE) = true :=
  CertificateChecks.KernelFi24P7.comm_word (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp))
    (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp)) MSp.A0_val MSp.S0_val MSp.cA0

theorem MS.b0s : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.B0 ++ J.S0) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (J.S0 ++ J.B0) CFSG.KD.BrFi24.ONE) = true :=
  CertificateChecks.KernelFi24P7.comm_word (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp))
    (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp)) MSp.B0_val MSp.S0_val MSp.cB0

theorem MS.t2s : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (J.T2 ++ J.S2) CFSG.KD.BrFi24.ONE)
    (wordMul CFSG.KD.BrFi24.MUL LG (J.S2 ++ J.T2) CFSG.KD.BrFi24.ONE) = true :=
  CertificateChecks.KernelFi24P7.comm_word (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp))
    (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp)) MSp.T2_val MSp.S2_val MSp.cT2

theorem MS.a2s : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG J.S2 (MX 0))
    (CFSG.KD.BrFi24.MUL (MX 0) (wordMul CFSG.KD.BrFi24.MUL LG J.S2 CFSG.KD.BrFi24.ONE)) = true :=
  CertificateChecks.KernelFi24P7.comm_mat (CertificateChecks.KernelFi24P7.msg_lt12 _ (by simp))
    (CertificateChecks.KernelSpor.Fi24Rels.hs.vld_q _ MSp.vld0) MSp.S2_val MSp.cA2

end CFSG.KD.Fi24P7

end
