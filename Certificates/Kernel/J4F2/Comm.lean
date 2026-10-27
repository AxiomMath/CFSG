module

public import CFSG.Quasithin.Background.F7TwoInvSporJ4Inputs
public import Certificates.Data.SmithB45ExcJ4C11
public import Certificates.Kernel.J4Q.MaskRep
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Q.QTBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CertificateChecks.KernelJ4Q

@[expose] noncomputable def E1 : Nat := etaK c rm one Us 1

theorem etaR1_enc : WfA (etaR 1) ∧ encR (etaR 1) = E1 := eta_enc 1

theorem gMat0_enc : WfA (gMat 0) ∧ encR (gMat 0) = A := base_gens 0

theorem gMat1_enc : WfA (gMat 1) ∧ encR (gMat 1) = B := base_gens 1

theorem gMat2_enc : WfA (gMat 2) ∧ encR (gMat 2) = Bi := base_invs 1

theorem gInv0_enc : WfA (gInv 0) ∧ encR (gInv 0) = Ai := base_invs 0

theorem gInv1_enc : WfA (gInv 1) ∧ encR (gInv 1) = Bi := base_invs 1

@[expose] noncomputable def CEA : Nat := mulJ c rm (mulJ c rm (mulJ c rm E1 A) E1) A

@[expose] noncomputable def CEB : Nat := mulJ c rm (mulJ c rm (mulJ c rm E1 B) E1) Bi

@[expose] noncomputable def CAB : Nat := mulJ c rm (mulJ c rm (mulJ c rm A B) A) Bi

theorem commEtaA_enc : WfA (CFSG.Quasithin.F7Two.j4CommEtaA ()) ∧
    encR (CFSG.Quasithin.F7Two.j4CommEtaA ()) = CEA :=
  mkMul (mkMul (mkMul etaR1_enc rowsA_enc) etaR1_enc) rowsA_enc

theorem commEtaB_enc : WfA (CFSG.Quasithin.F7Two.j4CommEtaB ()) ∧
    encR (CFSG.Quasithin.F7Two.j4CommEtaB ()) = CEB :=
  mkMul (mkMul (mkMul etaR1_enc rowsB_enc) etaR1_enc) gMat2_enc

theorem commAB_enc : WfA (CFSG.Quasithin.F7Two.j4CommAB ()) ∧
    encR (CFSG.Quasithin.F7Two.j4CommAB ()) = CAB :=
  mkMul (mkMul (mkMul rowsA_enc rowsB_enc) rowsA_enc) gMat2_enc

@[expose] noncomputable def C11K : Nat :=
  mulJ c rm E1 (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm Ai Bi) Ai) E1)
    (mulJ c rm (mulJ c rm A B) A))

theorem c11_enc : WfA (CFSG.Quasithin.B45Exc.C11 ()) ∧ encR (CFSG.Quasithin.B45Exc.C11 ()) = C11K :=
  mkMul etaR1_enc (mkMul (mkMul (mkMul (mkMul gInv0_enc gInv1_enc) gInv0_enc) etaR1_enc)
    (mkMul (mkMul gMat0_enc gMat1_enc) gMat0_enc))

theorem cea5 : Nat.beq (powJ c rm one CEA 5) one = true := by quickRfl
theorem cea1n : neN (powJ c rm one CEA 1) one = true := by quickRfl
theorem cea1 : Nat.beq (powJ c rm one CEA 1) one = false := beq_false cea1n
theorem ceb30 : Nat.beq (powJ c rm one CEB 30) one = true := by quickRfl
theorem ceb2n : neN (powJ c rm one CEB 2) one = true := by quickRfl
theorem ceb2 : Nat.beq (powJ c rm one CEB 2) one = false := beq_false ceb2n
theorem cab10 : Nat.beq (powJ c rm one CAB 10) one = true := by quickRfl
theorem cab2n : neN (powJ c rm one CAB 2) one = true := by quickRfl
theorem cab2 : Nat.beq (powJ c rm one CAB 2) one = false := beq_false cab2n
theorem c11_11 : Nat.beq (powJ c rm one C11K 11) one = true := by quickRfl
theorem c11_1n : neN C11K one = true := by quickRfl
theorem c11_1 : Nat.beq C11K one = false := beq_false c11_1n

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.F7Two in
theorem c7401 : (eqRows (powRows (j4CommEtaA ()) 5) idRows = true)
    ∧ (eqRows (powRows (j4CommEtaA ()) 1) idRows = false)
    ∧ (wfRows (powRows (j4CommEtaA ()) 1) = true)
    ∧ (eqRows (powRows (j4CommEtaB ()) 30) idRows = true)
    ∧ (eqRows (powRows (j4CommEtaB ()) 2) idRows = false)
    ∧ (wfRows (powRows (j4CommEtaB ()) 2) = true)
    ∧ (eqRows (powRows (j4CommAB ()) 10) idRows = true)
    ∧ (eqRows (powRows (j4CommAB ()) 2) idRows = false)
    ∧ (wfRows (powRows (j4CommAB ()) 2) = true)
    ∧ (wfRows idRows = true) := by
  rw [mkEq (mkPow commEtaA_enc 5) mkId, mkEq (mkPow commEtaA_enc 1) mkId,
    mkEq (mkPow commEtaB_enc 30) mkId, mkEq (mkPow commEtaB_enc 2) mkId,
    mkEq (mkPow commAB_enc 10) mkId, mkEq (mkPow commAB_enc 2) mkId]
  exact ⟨cea5, cea1, wf_bool (mkPow commEtaA_enc 1).1, ceb30, ceb2, wf_bool (mkPow commEtaB_enc 2).1,
    cab10, cab2, wf_bool (mkPow commAB_enc 2).1, wf_bool mkId.1⟩

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.B45Exc in
theorem c260381 : eqRows (powRows (C11 ()) 11) idRows = true ∧ eqRows (C11 ()) idRows = false ∧
    wfRows (C11 ()) = true := by
  rw [mkEq (mkPow c11_enc 11) mkId, mkEq c11_enc mkId]
  exact ⟨c11_11, c11_1, wf_bool c11_enc.1⟩

end CertificateChecks.KernelJ4F2

end
