module

public import Certificates.Kernel.J4Loc.I5Chk
public import Certificates.Kernel.J4Q.LocM
public import Certificates.Data.J4Loc.TrioOct

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Loc

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2 CertificateChecks.KernelJ4Q CFSG.Quasithin.J4Loc

theorem m5_enc : WfA (pathRows (repPaths.getD 5 [])) ∧
    encR (pathRows (repPaths.getD 5 [])) = getN one MLs 4 :=
  pathM_enc (i := 4) (by norm_num)

theorem m5i_enc : WfA (invRows (pathRows (repPaths.getD 5 []))) ∧
    encR (invRows (pathRows (repPaths.getD 5 []))) = getN one MLIs 4 ∧
    Nat.beq (mulJ c rm (getN one MLs 4) (getN one MLIs 4)) one = true :=
  pathMi_enc (i := 4) (by norm_num)

theorem k4177_rows {k : ℕ} (hk : k < 3) :
    eqRows (mulRows (mulRows (pathRows (repPaths.getD 5 []))
      (etaRows (uTab (locMats ()) (locInvs ())) 11 (getN 0 [965, 1979, 165] k)))
      (invRows (pathRows (repPaths.getD 5 []))))
      (etaRows (uTab (locMats ()) (locInvs ())) 11 (getN 0 [1243, 1979, 165] k)) = true := by
  rw [eqRows_of (mul_enc hK (mul_enc hK m5_enc (eta_enc _)) ⟨m5i_enc.1, m5i_enc.2.1⟩)
    (eta_enc _)]
  exact allR_spec ch4177_mat k hk

end CertificateChecks.KernelJ4Loc

end
