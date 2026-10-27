
module

public import Certificates.Kernel.Fi23M.Facts
public import Certificates.Kernel.Fi23M.WGlue
public import Certificates.Kernel.Fi23K.Orb

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23M

open CFSG.F3.Native CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.KD.Fi23K CFSG.KD.Fi23M
  CFSG.Sporadic.Th.Native CFSG.KC.Fi23K CFSG.KS.Mat3

theorem canonM_matD : canonM 253 (toVM matD) = true := by
  unfold matD
  exact canonM_powW (prodW_facts dWord dWord_lt).2.1 (canonM_prodW dWord dWord_lt) 7

theorem canonM_matE : canonM 253 (toVM matE) = true := by
  unfold matE
  exact canonM_prodW eWord eWord_lt

theorem matrixChecks_true : matrixChecks () = true := by
  have hM := matrixFacts
  obtain ⟨hDs, hDw, hDm⟩ := matD_facts
  obtain ⟨-, hEw, hEm⟩ := matE_facts
  have i1 : eqW 253 (mulW 253 matA matA) (idW 253) = true :=
    eqW_of_toMatW (by rw [mulW_size, matA_size])
      (canonW_of_canonM (canonM_mulW matA_size rowsWF_matA canonM_matA)) canonW_idW'
      (by rw [toMatW_mulW matA_size rowsWF_matA rowsWF_matA, toMatW_matA, toMatW_idW]; exact hM.A_sq)
  have i2 : eqW 253 (mulW 253 matB matBi) (idW 253) = true :=
    eqW_of_toMatW (by rw [mulW_size, matB_size])
      (canonW_of_canonM (canonM_mulW matB_size rowsWF_matB
        (canonM_mulW matB_size rowsWF_matB canonM_matB))) canonW_idW'
      (by rw [toMatW_mulW matB_size rowsWF_matB rowsWF_matBi, toMatW_matB, toMatW_matBi,
        toMatW_idW]; exact hM.B_inv)
  have i3 : eqW 253 (powW 253 matE 5) (idW 253) = true :=
    eqW_of_toMatW (powW_size _ 5) (canonW_of_canonM (canonM_powW hEw canonM_matE 5)) canonW_idW'
      (by rw [toMatW_powW hEw, hEm, toMatW_idW]; exact hM.E_pow)
  have i4 : eqW 253 (mulW 253 matD matD) (idW 253) = true :=
    eqW_of_toMatW (by rw [mulW_size, hDs]) (canonW_of_canonM (canonM_mulW hDs hDw canonM_matD))
      canonW_idW' (by rw [toMatW_mulW hDs hDw hDw, hDm, toMatW_idW]; exact hM.D_sq)
  have n1 : eqW 253 matA (idW 253) = false :=
    eqW_false_of_toMatW (by rw [toMatW_matA, toMatW_idW]; exact hM.A_ne)
  have n2 : eqW 253 matB (idW 253) = false :=
    eqW_false_of_toMatW (by rw [toMatW_matB, toMatW_idW]; exact hM.B_ne)
  have n3 : eqW 253 matD (idW 253) = false :=
    eqW_false_of_toMatW (by rw [hDm, toMatW_idW]; exact hM.D_ne)
  unfold matrixChecks
  rw [canonW_matA, canonW_matB, canonW_idW', canonW_matD, i1, i2, i3, i4, n1, n2, n3]
  rfl

theorem keys_get {i : Nat} (hi : i < 31671) : orbLit.keys[i]! = keyW 200 i := by
  unfold orbLit
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem tb92_1 : tb G 92 1 = 1 := by decide +kernel
theorem tb91_1 : tb G 91 1 = 0 := by decide +kernel
theorem tb92_2 : tb G 92 2 = 2 := by decide +kernel
theorem tb91_2 : tb G 91 2 = 0 := by decide +kernel

theorem keyW_zero (f : Nat) : keyW f 0 = matD := by
  cases f <;> rfl

theorem key1 : keyW 200 1 = conjW 253 matA matA matD := by
  have e : keyW 200 1 = if (1 : Nat) = 0 then matD else if tb G 92 1 = 1 then
      conjW 253 matA matA (keyW 199 (tb G 91 1)) else conjW 253 matB matBi (keyW 199 (tb G 91 1)) :=
    rfl
  rw [e, if_neg (by decide), if_pos tb92_1, tb91_1, keyW_zero]

theorem key2 : keyW 200 2 = conjW 253 matB matBi matD := by
  have e : keyW 200 2 = if (2 : Nat) = 0 then matD else if tb G 92 2 = 1 then
      conjW 253 matA matA (keyW 199 (tb G 91 2)) else conjW 253 matB matBi (keyW 199 (tb G 91 2)) :=
    rfl
  rw [e, if_neg (by decide), if_neg (by rw [tb92_2]; decide), tb91_2, keyW_zero]

theorem conjW_size {g gi X : Array W} (hg : g.size = 253) : (conjW 253 g gi X).size = 253 := by
  unfold conjW
  rw [mulW_size, mulW_size, hg]

theorem RowsWF.conjW {g gi X : Array W} (hg : RowsWF (toVM g)) (hgi : RowsWF (toVM gi))
    (hX : RowsWF (toVM X)) : RowsWF (toVM (conjW 253 g gi X)) :=
  RowsWF.mulW (RowsWF.mulW hg hX) hgi

theorem canonM_conjW {g gi X : Array W} (hgs : g.size = 253) (hg : RowsWF (toVM g))
    (hX : RowsWF (toVM X)) (hgi : canonM 253 (toVM gi) = true) :
    canonM 253 (toVM (conjW 253 g gi X)) = true := by
  unfold conjW
  exact canonM_mulW (by rw [mulW_size, hgs]) (RowsWF.mulW hg hX) hgi

theorem canonM_matBi : canonM 253 (toVM matBi) = true := by
  unfold matBi
  exact canonM_mulW matB_size rowsWF_matB canonM_matB

theorem toMatW_key1 : toMatW 253 (keyW 200 1) = mat3 253 64009 (RS 3) := by
  rw [key1, toMatW_conjW matA_size rowsWF_matA rowsWF_matA matD_facts.2.1, toMatW_matA,
    matD_facts.2.2, mat_K1]

theorem toMatW_key2 : toMatW 253 (keyW 200 2) = mat3 253 64009 (RS 4) := by
  rw [key2, toMatW_conjW matB_size rowsWF_matB rowsWF_matBi matD_facts.2.1, toMatW_matB,
    toMatW_matBi, matD_facts.2.2, mat_K2]

theorem productChecks_true : productChecks orbLit = true := by
  obtain ⟨hDs, hDw, hDm⟩ := matD_facts
  obtain ⟨p1, n1, p2, n2⟩ := prodFacts
  have w1 : RowsWF (toVM (keyW 200 1)) := by
    rw [key1]; exact RowsWF.conjW rowsWF_matA rowsWF_matA hDw
  have w2 : RowsWF (toVM (keyW 200 2)) := by
    rw [key2]; exact RowsWF.conjW rowsWF_matB rowsWF_matBi hDw
  have c1 : canonM 253 (toVM (keyW 200 1)) = true := by
    rw [key1]; exact canonM_conjW matA_size rowsWF_matA hDw canonM_matA
  have c2 : canonM 253 (toVM (keyW 200 2)) = true := by
    rw [key2]; exact canonM_conjW matB_size rowsWF_matB hDw canonM_matBi
  have cP1 := canonM_mulW (Y := keyW 200 1) hDs hDw c1
  have cP2 := canonM_mulW (Y := keyW 200 2) hDs hDw c2
  have wP1 : RowsWF (toVM (mulW 253 matD (keyW 200 1))) := RowsWF.mulW hDw w1
  have wP2 : RowsWF (toVM (mulW 253 matD (keyW 200 2))) := RowsWF.mulW hDw w2
  have mP1 : toMatW 253 (mulW 253 matD (keyW 200 1)) = mat3 253 64009 (RS 8) := by
    rw [toMatW_mulW hDs hDw w1, hDm, toMatW_key1, mat_P1]
  have mP2 : toMatW 253 (mulW 253 matD (keyW 200 2)) = mat3 253 64009 (RS 9) := by
    rw [toMatW_mulW hDs hDw w2, hDm, toMatW_key2, mat_P2]
  have e1 : eqW 253 (powW 253 (mulW 253 matD (keyW 200 1)) 2) (idW 253) = true :=
    eqW_of_toMatW (powW_size _ 2) (canonW_of_canonM (canonM_powW wP1 cP1 2)) canonW_idW'
      (by rw [toMatW_powW wP1, mP1, toMatW_idW, sq]; exact p1)
  have e2 : eqW 253 (powW 253 (mulW 253 matD (keyW 200 2)) 3) (idW 253) = true :=
    eqW_of_toMatW (powW_size _ 3) (canonW_of_canonM (canonM_powW wP2 cP2 3)) canonW_idW'
      (by rw [toMatW_powW wP2, mP2, toMatW_idW, pow_three']; exact p2)
  have f1 : eqW 253 (mulW 253 matD (keyW 200 1)) (idW 253) = false :=
    eqW_false_of_toMatW (by rw [mP1, toMatW_idW]; exact n1)
  have f2 : eqW 253 (mulW 253 matD (keyW 200 2)) (idW 253) = false :=
    eqW_false_of_toMatW (by rw [mP2, toMatW_idW]; exact n2)
  have hsub : subRoot () = 2 := rfl
  unfold productChecks
  rw [hsub, keys_get (by norm_num), keys_get (by norm_num)]
  dsimp only
  rw [canonW_of_canonM cP1, canonW_of_canonM cP2, e1, e2, f1, f2]
  rfl

end CertificateChecks.KernelFi23M

end
