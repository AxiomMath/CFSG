module

public import CFSG.Milestones.ASVolI.C31.J4NP.Is2ANative
public import Certificates.Kernel.J4F2.J4Std
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTRankWitNative

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CertificateChecks.KernelJ4Q

theorem v2N_eq_toNat' (a : V2) : v2N a = a.lo.toNat + 2 ^ 64 * a.hi.toNat := by
  unfold v2N
  rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt a.lo) a.hi.toNat, Nat.shiftLeft_eq]
  omega

@[expose] noncomputable def rowsArr (M : Nat) : Array Nat := (List.range 112).toArray.map (rowJ rm M)

theorem natRows_eq {X : Array V2} (hX : WfA X) :
    CFSG.ASVolI.burnsideJ4NP_natRows X = rowsArr (encR X) := by
  unfold CFSG.ASVolI.burnsideJ4NP_natRows rowsArr
  apply Array.ext
  · simp [hX.1]
  · intro i h1 h2
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range]
    have hi : i < X.size := by simpa using h1
    rw [← v2N_eq_toNat', ← v2N_getElem! hK hX i, getElem!_pos X i hi]

@[expose] noncomputable def rowFixK (M k : Nat) : Bool :=
  CFSG.Quasithin.H13.NQCat.Native.fixDimOK 112 (rowsArr (trJ t0 t1 t2 t3 t4 t5 t6 M)) k

theorem fix1_chk : rowFixK (eK 1) 56 = true := by
  unfold rowFixK CFSG.Quasithin.H13.NQCat.Native.fixDimOK CFSG.Quasithin.H13.NQCat.Native.fixCertOK
    CFSG.Quasithin.H13.NQCat.Native.rrefOK
  simp only [← Array.all_toList]
  quickRfl

theorem fix1131_chk : rowFixK (eK 1131) 62 = true := by
  unfold rowFixK CFSG.Quasithin.H13.NQCat.Native.fixDimOK CFSG.Quasithin.H13.NQCat.Native.fixCertOK
    CFSG.Quasithin.H13.NQCat.Native.rrefOK
  simp only [← Array.all_toList]
  quickRfl

theorem rowFix_eq {X : Array V2} {x : Nat} (hX : WfA X ∧ encR X = x) (k : Nat) :
    CFSG.ASVolI.burnsideJ4NP_rowFixOK X k = rowFixK x k := by
  unfold CFSG.ASVolI.burnsideJ4NP_rowFixOK rowFixK
  rw [natRows_eq (wf_transposeRows X), enc_transposeRows hK hX.1, hX.2]

theorem c7852 : CFSG.ASVolI.burnsideJ4NP_fixOK () = true := by
  unfold CFSG.ASVolI.burnsideJ4NP_fixOK CFSG.ASVolI.burnsideJ4NP_fixOKOf etaRT
  rw [rowFix_eq (etaU_enc 1), rowFix_eq (etaU_enc 1131), fix1_chk, fix1131_chk]
  rfl

end CertificateChecks.KernelJ4F2

end
