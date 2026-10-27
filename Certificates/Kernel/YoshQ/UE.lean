module

public import Certificates.Kernel.YoshQ.DataN
public import Certificates.Kernel.YoshQ.DataW
public import Certificates.Data.Kernel.YoshQ.Twin
public import CFSG.Certificates.Kernel.YoshQ.UEFSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Eval
public import Certificates.Kernel.Sporadic.OrbRecGen
meta import Certificates.Kernel.YoshQ.UEGen
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
public import CFSG.Certificates.Kernel.YoshQ.ParamSound
public import CFSG.Certificates.Kernel.YoshQ.TwinSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh

set_option maxHeartbeats 0

#kc_eval CertificateChecks.KernelYoshQ U00 CertificateChecks.KernelYoshQ.ueStep 0 0
#kc_eval CertificateChecks.KernelYoshQ U01 CertificateChecks.KernelYoshQ.ueStep 0 1
#kc_eval CertificateChecks.KernelYoshQ U10 CertificateChecks.KernelYoshQ.ueStep 1 0
#kc_eval CertificateChecks.KernelYoshQ U11 CertificateChecks.KernelYoshQ.ueStep 1 1
#kc_nattree CertificateChecks.KernelYoshQ.U00.T CertificateChecks.KernelYoshQ.ueTab00
#kc_nattree CertificateChecks.KernelYoshQ.U01.T CertificateChecks.KernelYoshQ.ueTab01
#kc_nattree CertificateChecks.KernelYoshQ.U10.T CertificateChecks.KernelYoshQ.ueTab10
#kc_nattree CertificateChecks.KernelYoshQ.U11.T CertificateChecks.KernelYoshQ.ueTab11

theorem u00t : ueT U00.P U00.M U00.T E00.RL = true := by quickRfl
theorem u00i : ueI E00.RL U00.LI U00.YL U00.YI = true := by quickRfl
theorem u00y : ueY U00.P U00.M U00.T (nTN N00.GS (swN cWord)) S00.RL U00.YL = true := by quickRfl
theorem u002 : ue2 U00.P U00.M U00.T E00.GS S00.RL = true := by quickRfl
theorem u005 : ue5 (nTN N00.GS (swN cWord)) E00.RL U00.LI = true := by quickRfl
theorem u00v : ueV (nTN N00.GS (swN cWord)) E00.RL U00.LI U00.YL U00.YI U00.MK = true := by
  quickRfl
theorem u008 : ue8 U00.P U00.M U00.T U00.YL U00.YI U00.MK = true := by quickRfl
theorem u00r : ueR E00.GS S00.GS (nTN N00.GS (swN cWord)) E00.RL S00.RL = true := by quickRfl

theorem u01t : ueT U01.P U01.M U01.T E01.RL = true := by quickRfl
theorem u01i : ueI E01.RL U01.LI U01.YL U01.YI = true := by quickRfl
theorem u01y : ueY U01.P U01.M U01.T (nTN N01.GS (swN cWord)) S01.RL U01.YL = true := by quickRfl
theorem u012 : ue2 U01.P U01.M U01.T E01.GS S01.RL = true := by quickRfl
theorem u015 : ue5 (nTN N01.GS (swN cWord)) E01.RL U01.LI = true := by quickRfl
theorem u01v : ueV (nTN N01.GS (swN cWord)) E01.RL U01.LI U01.YL U01.YI U01.MK = true := by
  quickRfl
theorem u018 : ue8 U01.P U01.M U01.T U01.YL U01.YI U01.MK = true := by quickRfl
theorem u01r : ueR E01.GS S01.GS (nTN N01.GS (swN cWord)) E01.RL S01.RL = true := by quickRfl

theorem u10t : ueT U10.P U10.M U10.T E10.RL = true := by quickRfl
theorem u10i : ueI E10.RL U10.LI U10.YL U10.YI = true := by quickRfl
theorem u10y : ueY U10.P U10.M U10.T (nTN N10.GS (swN cWord)) S10.RL U10.YL = true := by quickRfl
theorem u102 : ue2 U10.P U10.M U10.T E10.GS S10.RL = true := by quickRfl
theorem u105 : ue5 (nTN N10.GS (swN cWord)) E10.RL U10.LI = true := by quickRfl
theorem u10v : ueV (nTN N10.GS (swN cWord)) E10.RL U10.LI U10.YL U10.YI U10.MK = true := by
  quickRfl
theorem u108 : ue8 U10.P U10.M U10.T U10.YL U10.YI U10.MK = true := by quickRfl
theorem u10r : ueR E10.GS S10.GS (nTN N10.GS (swN cWord)) E10.RL S10.RL = true := by quickRfl

theorem u11t : ueT U11.P U11.M U11.T E11.RL = true := by quickRfl
theorem u11i : ueI E11.RL U11.LI U11.YL U11.YI = true := by quickRfl
theorem u11y : ueY U11.P U11.M U11.T (nTN N11.GS (swN cWord)) S11.RL U11.YL = true := by quickRfl
theorem u112 : ue2 U11.P U11.M U11.T E11.GS S11.RL = true := by quickRfl
theorem u115 : ue5 (nTN N11.GS (swN cWord)) E11.RL U11.LI = true := by quickRfl
theorem u11v : ueV (nTN N11.GS (swN cWord)) E11.RL U11.LI U11.YL U11.YI U11.MK = true := by
  quickRfl
theorem u118 : ue8 U11.P U11.M U11.T U11.YL U11.YI U11.MK = true := by quickRfl
theorem u11r : ueR E11.GS S11.GS (nTN N11.GS (swN cWord)) E11.RL S11.RL = true := by quickRfl

theorem ue00 : ueN E00.GS S00.GS (nTN N00.GS (swN cWord)) E00.RL S00.RL = true :=
  ueN_of_F u00t u00i u00y u002 u005 u00v u008 u00r
theorem ue01 : ueN E01.GS S01.GS (nTN N01.GS (swN cWord)) E01.RL S01.RL = true :=
  ueN_of_F u01t u01i u01y u012 u015 u01v u018 u01r
theorem ue10 : ueN E10.GS S10.GS (nTN N10.GS (swN cWord)) E10.RL S10.RL = true :=
  ueN_of_F u10t u10i u10y u102 u105 u10v u108 u10r
theorem ue11 : ueN E11.GS S11.GS (nTN N11.GS (swN cWord)) E11.RL S11.RL = true :=
  ueN_of_F u11t u11i u11y u112 u115 u11v u118 u11r

theorem es_all :
    esN E00.GS S00.GS (nTN N00.GS (swN cWord)) E00.RL S00.RL N00.GS = true ∧
    esN E01.GS S01.GS (nTN N01.GS (swN cWord)) E01.RL S01.RL N01.GS = true ∧
    esN E10.GS S10.GS (nTN N10.GS (swN cWord)) E10.RL S10.RL N10.GS = true ∧
    esN E11.GS S11.GS (nTN N11.GS (swN cWord)) E11.RL S11.RL N11.GS = true := by
  decide +kernel

end CertificateChecks.KernelYoshQ

end
