module

public import Certificates.Kernel.U52.Letters
public import Certificates.Kernel.U52.NormData
public import Certificates.Data.Kernel.U52.Norm
public import Certificates.Data.Kernel.Spor.WordF
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelU52

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.WordF CFSG.KS.U52N CertificateChecks.KernelU52.N

@[expose] noncomputable def nKL : List Nat :=
  burnsideF48t_u52KW.map (evFK 462 9 (mask 9) (pidn 462 9) LP LPI)

@[expose] noncomputable def nKG : List Nat := [nKL.getD 1 0, nKL.getD 3 0]

@[expose] noncomputable def nRisX : List Nat :=
  burnsideF48t_u52XW.map fun w => evFK 462 9 (mask 9) (pidn 462 9) LP LPI (burnsideF48s_eInvW w)

@[expose] noncomputable def nRisY : List Nat :=
  burnsideF48t_u52YW.map fun w => evFK 462 9 (mask 9) (pidn 462 9) LP LPI (burnsideF48s_eInvW w)

@[expose] noncomputable def okB (l : Nat) : Bool := Nat.blt l 2

@[expose] noncomputable def okP1 (l : Nat) : Bool := Nat.blt l 3

@[expose] noncomputable def okP2 (l : Nat) : Bool := Nat.blt l 2 || Nat.beq l 3

theorem nK : kOK 462 9 (mask 9) (pidn 462 9) nKL nKG NF = true := by quickRfl

theorem nTreeB : treeOK 462 9 (mask 9) LP okB NF OBN OBP OBG = true := by quickRfl
theorem nTreeP1 : treeOK 462 9 (mask 9) LP okP1 NF OP1N OP1P OP1G = true := by quickRfl
theorem nTreeP2 : treeOK 462 9 (mask 9) LP okP2 NF OP2N OP2P OP2G = true := by quickRfl

theorem nGensB : gensOK 462 9 (mask 9) (pidn 462 9) LP okB SVB SWB = true := by quickRfl
theorem nGensP1 : gensOK 462 9 (mask 9) (pidn 462 9) LP okP1 SVP1 SWP1 = true := by quickRfl
theorem nGensP2 : gensOK 462 9 (mask 9) (pidn 462 9) LP okP2 SVP2 SWP2 = true := by quickRfl

theorem nStabB : stabOK 462 9 (mask 9) (pidn 462 9) NF SVB EWB = true := by quickRfl
theorem nStabP1 : stabOK 462 9 (mask 9) (pidn 462 9) NF SVP1 EWP1 = true := by quickRfl
theorem nStabP2 : stabOK 462 9 (mask 9) (pidn 462 9) NF SVP2 EWP2 = true := by quickRfl

theorem nPref : OBN.length = 256 ∧ OP1N.length = 768 ∧ OP2N.length = 640 ∧ EWB.length = 36 ∧
    EWP1.length = 108 ∧ EWP2.length = 72 ∧ SVB.length = 3 ∧
    ((EWP1.take 36).all fun ew => ew.all fun c => Nat.blt c 3) = true ∧
    ((EWP2.take 36).all fun ew => ew.all fun c => Nat.blt c 3) = true ∧
    ((SWP1.take 3).all fun ws => ws.all okB) = true ∧
    ((SWP2.take 3).all fun ws => ws.all okB) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem nTestP1 : ((elems 462 9 (mask 9) (pidn 462 9) SVP1 EWP1).drop 36).all
    (cosetT 462 9 (mask 9) nKL nRisX) = true := by quickRfl

theorem nTestP2 : ((elems 462 9 (mask 9) (pidn 462 9) SVP2 EWP2).drop 36).all
    (cosetT 462 9 (mask 9) nKL nRisY) = true := by quickRfl

end CertificateChecks.KernelU52

end
