module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.ONPv.Data
public import Certificates.Kernel.Sporadic.ONPl.Data
public import Certificates.Data.Kernel.Spor.ONPlK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPl

open CFSG.KS.ONPl CertificateChecks.KernelSpor.ON

theorem ln_b0a : plLnR TT UU OPV.D OPL.D (nat_lit 0) (nat_lit 7) (nat_lit 0) = true := by quickRfl
theorem ln_b0b : plLnR TT UU OPV.D OPL.D (nat_lit 7) (nat_lit 7) (nat_lit 0) = true := by quickRfl
theorem ln_b1a : plLnR TT UU OPV.D OPL.D (nat_lit 0) (nat_lit 7) (nat_lit 227759) = true := by
  quickRfl
theorem ln_b1b : plLnR TT UU OPV.D OPL.D (nat_lit 7) (nat_lit 7) (nat_lit 227759) = true := by
  quickRfl
theorem ln_b2a : plLnR TT UU OPV.D OPL.D (nat_lit 0) (nat_lit 7) (nat_lit 100817) = true := by
  quickRfl
theorem ln_b2b : plLnR TT UU OPV.D OPL.D (nat_lit 7) (nat_lit 7) (nat_lit 100817) = true := by
  quickRfl

theorem al_b0a : plAlR TT UU OPV.D OPL.D (nat_lit 14) (nat_lit 7) (nat_lit 0) = true := by quickRfl
theorem al_b0b : plAlR TT UU OPV.D OPL.D (nat_lit 21) (nat_lit 7) (nat_lit 0) = true := by quickRfl
theorem al_b1a : plAlR TT UU OPV.D OPL.D (nat_lit 14) (nat_lit 7) (nat_lit 227759) = true := by
  quickRfl
theorem al_b1b : plAlR TT UU OPV.D OPL.D (nat_lit 21) (nat_lit 7) (nat_lit 227759) = true := by
  quickRfl
theorem al_b2a : plAlR TT UU OPV.D OPL.D (nat_lit 14) (nat_lit 7) (nat_lit 100817) = true := by
  quickRfl
theorem al_b2b : plAlR TT UU OPV.D OPL.D (nat_lit 21) (nat_lit 7) (nat_lit 100817) = true := by
  quickRfl

theorem x_b0 : plX TT UU OPV.D OPL.D (nat_lit 0) = true := by quickRfl
theorem x_b1 : plX TT UU OPV.D OPL.D (nat_lit 227759) = true := by quickRfl
theorem x_b2 : plX TT UU OPV.D OPL.D (nat_lit 100817) = true := by quickRfl

theorem p_b0 : plP TT UU OPV.D OPL.D (nat_lit 0) = true := by quickRfl
theorem p_b1 : plP TT UU OPV.D OPL.D (nat_lit 227759) = true := by quickRfl
theorem p_b2 : plP TT UU OPV.D OPL.D (nat_lit 100817) = true := by quickRfl

theorem hd : plHd TT UU OPV.D OPL.D = true := by quickRfl

end CertificateChecks.KernelSpor.ONPl

end
