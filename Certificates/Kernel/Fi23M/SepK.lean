module

public import Certificates.Kernel.Fi23M.Data
public import Certificates.Data.CFSGNative.Fi23.Data
public import CFSG.Certificates.Kernel.Spor.F3LaneSepSound
public import CFSG.Certificates.Kernel.Spor.F3R

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23M

open CFSG.F3.Native CFSG.KS.F3L CFSG.KS.F3R CFSG.KD.Fi23M CFSG.Sporadic.Fi23.Native

@[expose] noncomputable def lane (X : Nat) : V := ⟨Nat.land X LO, Nat.shiftRight X 64009⟩

@[expose] noncomputable def LsS : List V :=
  [lane (RS 1), lane (RS 3), lane (RS 4), lane (RS 5), lane (RS 6), lane (RS 7)]

@[expose] noncomputable def LI : V := lane ONE

@[expose] noncomputable def WL : V := combL 253 (spreadE 253 253) LI LsS sepTerms

set_option Elab.async false

theorem LI_wf : LI.wf = true := by decide +kernel

theorem id_ok : eqMK 253 (idM 253) (unlane 253 LI) = true := by decide +kernel

theorem idM_eq : idM 253 = unlane 253 LI := by
  have h : eqM 253 (idM 253) (unlane 253 LI) = true := by rw [eqM_eq]; exact id_ok
  exact eq_of_canonM (canonM_idM 253) (canonM_unlane 253 LI_wf) (toMat_eq_of_eqM h)

theorem LsS_wf' : LsS.all V.wf = true := by decide +kernel

theorem LsS_wf : ∀ L ∈ LsS, L.wf = true := by
  intro L hL
  exact List.all_eq_true.1 LsS_wf' L hL

theorem wl_wf : WL.wf = true := by decide +kernel

theorem vec_lt : (sepVec ()).p < 2 ^ 253 ∧ (sepVec ()).m < 2 ^ 253 := by decide

theorem sepK_ok : sepOK 253 (LsS.map (unlane 253)).toArray sepTerms (sepVec ()) (sepK ())
    (sepP ()) (sepTinv ()) sepTree = true := by
  have hd : 0 < 253 := by norm_num
  unfold sepOK
  rw [combM_unlane hd idM_eq LsS sepTerms (by decide), spinVecs_lane hd LsS_wf vec_lt.1 vec_lt.2
    sepTree (by decide)]
  change (_ && (mulVecM 253 (unlane 253 WL) (sepVec ())).isZero && _ && _ && _ && _ && _) = true
  rw [mulVec_unlane hd wl_wf vec_lt.1 vec_lt.2]
  simp only [mul_eq, eqM_eq, wfM_eq, ← Array.all_toList]
  decide +kernel

end CertificateChecks.KernelFi23M

end
