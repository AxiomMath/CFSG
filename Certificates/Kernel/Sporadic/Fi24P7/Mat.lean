module

public import Certificates.Kernel.Sporadic.Fi24F3d.Adj
public import CFSG.Certificates.Kernel.Spor.Fi24KnSound
public import CFSG.Certificates.Kernel.Spor.Fi24G2eSound
public import Certificates.Kernel.Sporadic.Fi24P7.Defs
public import Certificates.Kernel.Sporadic.Fi24P7.MS

public section

namespace CertificateChecks.KernelFi24P7

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 CertificateChecks.KernelFi24Fix
  CertificateChecks.KernelFi24Orb CertificateChecks.KernelFi24G2e CertificateChecks.KernelFi24Ext
  CertificateChecks.KernelFi24F3d CFSG.KC.Loop CFSG.KC.Fi24G2eS CFSG.KC.Fi24Kn CFSG.KC.Fi24KnS
  CFSG.KD.Fi24G2e CFSG.KD.Fi24P7

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24G2e.BX CFSG.KD.Fi24Ext.MX CFSG.KD.BrFi24.MT
  CFSG.KD.Fi24Fix.MX CFSG.KD.Fi24P7.MX CFSG.KD.BrFi24.ONE CFSG.KD.BrFi24.MUL

theorem eq_of_beq' {X Y : ℕ} (h : Nat.beq X Y = true) : X = Y := Nat.eq_of_beq_eq_true h

theorem xw_mat {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {M : ℕ}
    (h : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w CFSG.KD.BrFi24.ONE) M = true) :
    Cn M ∧ ((xw w : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt M := by
  obtain ⟨h1, h2⟩ := wordMul_τ cn_one w hw
  rw [eq_of_beq' h] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, mt_one, Matrix.mul_one]

theorem xw_eq_beq {u v : List ℕ} (hu : ∀ g ∈ u, g < 12) (hv : ∀ g ∈ v, g < 12)
    (h : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG u CFSG.KD.BrFi24.ONE)
      (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG v CFSG.KD.BrFi24.ONE) = true) : xw u = xw v := by
  obtain ⟨-, h1⟩ := xw_mat hu h
  obtain ⟨-, h2⟩ := wordMul_τ cn_one v hv
  refine Units.ext (h1.trans ?_)
  rw [h2, mt_one, Matrix.mul_one]

theorem xw_one_beq {u : List ℕ} (hu : ∀ g ∈ u, g < 12)
    (h : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG u CFSG.KD.BrFi24.ONE)
      CFSG.KD.BrFi24.ONE = true) : xw u = 1 := by
  obtain ⟨-, h1⟩ := xw_mat hu h
  refine Units.ext ?_
  rw [h1, mt_one, Units.val_one]

theorem mt_pow7 {M : ℕ} (hM : Cn M) : Mt (pow7 M) = Mt M ^ 7 := by
  unfold pow7
  rw [strictN_eqE, strictN_eqE]
  obtain ⟨c2, e2⟩ := mul_mt hM hM
  obtain ⟨c4, e4⟩ := mul_mt c2 c2
  obtain ⟨c6, e6⟩ := mul_mt c4 c2
  rw [(mul_mt c6 hM).2, e6, e4, e2]
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]

theorem mt_pow3 {M : ℕ} (hM : Cn M) : Mt (pow3 M) = Mt M ^ 3 := by
  unfold pow3
  rw [strictN_eqE]
  obtain ⟨c2, e2⟩ := mul_mt hM hM
  rw [(mul_mt c2 hM).2, e2]
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]

theorem pow7_of_mat {x : GL (Fin 781) (ZMod 3)} {M : ℕ} (hc : Cn M)
    (hv : (x : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt M)
    (h7 : Nat.beq (pow7 M) CFSG.KD.BrFi24.ONE = true) : x ^ 7 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, hv, ← mt_pow7 hc, eq_of_beq' h7, mt_one, Units.val_one]

theorem pow3_of_mat {x : GL (Fin 781) (ZMod 3)} {M : ℕ} (hc : Cn M)
    (hv : (x : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt M)
    (h3 : Nat.beq (pow3 M) CFSG.KD.BrFi24.ONE = true) : x ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, hv, ← mt_pow3 hc, eq_of_beq' h3, mt_one, Units.val_one]

theorem chain_step {p : List ℕ} (hp : ∀ g ∈ p, g < 12) {Y Z : ℕ} {y : GL (Fin 781) (ZMod 3)}
    (hY : Cn Y) (hy : (y : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt Y)
    (h : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG p Y) Z = true) :
    Cn Z ∧ ((xw p * y : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt Z := by
  obtain ⟨c1, v1⟩ := wordMul_τ hY p hp
  rw [eq_of_beq' h] at c1 v1
  refine ⟨c1, ?_⟩
  rw [Units.val_mul, v1, hy]

theorem chain_mat {P : List (List ℕ)} {b k : ℕ} (hk : 0 < k) (hP : P.length = k)
    (hlt : ∀ p ∈ P, ∀ g ∈ p, g < 12) (h : ∀ i < k, chStep P b k i = true) :
    Cn (CFSG.KD.Fi24P7.MX b) ∧
      ((xw P.flatten : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
        Mt (CFSG.KD.Fi24P7.MX b) := by
  have key : ∀ n, 0 < n → n ≤ k → Cn (CFSG.KD.Fi24P7.MX (b + (k - n))) ∧
      ((xw (P.drop (k - n)).flatten : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
        Mt (CFSG.KD.Fi24P7.MX (b + (k - n))) := by
    intro n hn0 hnk
    induction n with
    | zero => omega
    | succ n ih =>
      set i := k - (n + 1) with hi
      have hil : i < P.length := by omega
      have hs := h i (by omega)
      unfold chStep at hs
      rw [nthW_eq, List.getD_eq_getElem _ _ hil] at hs
      have hpl : ∀ g ∈ P[i], g < 12 := hlt _ (List.getElem_mem _)
      have e : P.drop i = P[i] :: P.drop (i + 1) := List.drop_eq_getElem_cons hil
      have hz : Nat.add b i = b + i := rfl
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        have hb : Nat.blt (Nat.succ i) k = false := by
          rw [Bool.eq_false_iff]
          intro hb
          have := Nat.le_of_ble_eq_true hb
          omega
        rw [hb] at hs
        have hd : P.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
        have hy : ((xw (P.drop (i + 1)).flatten : GL (Fin 781) (ZMod 3)) :
            Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt CFSG.KD.BrFi24.ONE := by
          rw [hd, mt_one]
          simp [xw, wq]
        obtain ⟨c1, v1⟩ := chain_step hpl cn_one hy hs
        rw [hz] at c1 v1
        refine ⟨c1, ?_⟩
        rw [e, List.flatten_cons, xw_append]
        exact v1
      · obtain ⟨cD, vD⟩ := ih h0 (by omega)
        have hb : Nat.blt (Nat.succ i) k = true := by simpa using (by omega : i + 1 < k)
        rw [hb] at hs
        have e2 : k - n = i + 1 := by omega
        rw [e2] at cD vD
        have hw : Nat.add b (Nat.succ i) = b + (i + 1) := rfl
        rw [hw] at hs
        obtain ⟨c1, v1⟩ := chain_step hpl cD vD hs
        rw [hz] at c1 v1
        refine ⟨c1, ?_⟩
        rw [e, List.flatten_cons, xw_append]
        exact v1
  obtain ⟨c, v⟩ := key k hk le_rfl
  rw [Nat.sub_self, Nat.add_zero, List.drop_zero] at *
  exact ⟨c, v⟩

end CertificateChecks.KernelFi24P7

end
