module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.LocalComp.SurjGen
public meta import Certificates.Data.GSThmBCatalog7CF24
public import CFSG.Open.LocalVocabulary

public section

namespace CertificateChecks.KernelSpor.CF24

open CFSG.ComponentClassification.GSThmB.CF24 CFSG.Sporadic.Recognition.SuzMultiplier
  CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native

meta def b0M : Array Nat := b0Arr
meta def b1M : Array Nat := b1Arr
meta def b0iM : Array Nat := invCand 1782 b0Arr
meta def b1iM : Array Nat := invCand 1782 b1Arr
meta def sg0M : Array Nat := suzGenArrs[0]!
meta def sg1M : Array Nat := suzGenArrs[1]!
meta def sg2M : Array Nat := suzGenArrs[2]!
meta def sg3M : Array Nat := suzGenArrs[3]!
meta def sg4M : Array Nat := suzGenArrs[4]!
meta def sg5M : Array Nat := suzGenArrs[5]!
meta def sg6M : Array Nat := suzGenArrs[6]!
meta def sgi0M : Array Nat := invCand 1782 suzGenArrs[0]!
meta def sgi1M : Array Nat := invCand 1782 suzGenArrs[1]!
meta def sgi2M : Array Nat := invCand 1782 suzGenArrs[2]!
meta def sgi3M : Array Nat := invCand 1782 suzGenArrs[3]!
meta def sgi4M : Array Nat := invCand 1782 suzGenArrs[4]!
meta def sgi5M : Array Nat := invCand 1782 suzGenArrs[5]!
meta def sgi6M : Array Nat := invCand 1782 suzGenArrs[6]!
meta def l0M : Array Nat := cf24EllArrs[0]!
meta def l1M : Array Nat := cf24EllArrs[1]!
meta def l2M : Array Nat := cf24EllArrs[2]!
meta def l3M : Array Nat := cf24EllArrs[3]!
meta def l4M : Array Nat := cf24EllArrs[4]!
meta def li0M : Array Nat := invCand 1782 cf24EllArrs[0]!
meta def li1M : Array Nat := invCand 1782 cf24EllArrs[1]!
meta def li2M : Array Nat := invCand 1782 cf24EllArrs[2]!
meta def li3M : Array Nat := invCand 1782 cf24EllArrs[3]!
meta def li4M : Array Nat := invCand 1782 cf24EllArrs[4]!
meta def xM : Array Nat := cf24XArr
meta def yM : Array Nat := cf24YArr
meta def omM : Array Nat := Array.ofFn (n := 1782) fun x => if cf24InO1 x.val then 1 else 0

end CertificateChecks.KernelSpor.CF24

#ks_perm CertificateChecks.KernelSpor.CF24.B0 11 CertificateChecks.KernelSpor.CF24.b0M
#ks_perm CertificateChecks.KernelSpor.CF24.B1 11 CertificateChecks.KernelSpor.CF24.b1M
#ks_perm CertificateChecks.KernelSpor.CF24.B0I 11 CertificateChecks.KernelSpor.CF24.b0iM
#ks_perm CertificateChecks.KernelSpor.CF24.B1I 11 CertificateChecks.KernelSpor.CF24.b1iM
#ks_perm CertificateChecks.KernelSpor.CF24.SG0 11 CertificateChecks.KernelSpor.CF24.sg0M
#ks_perm CertificateChecks.KernelSpor.CF24.SG1 11 CertificateChecks.KernelSpor.CF24.sg1M
#ks_perm CertificateChecks.KernelSpor.CF24.SG2 11 CertificateChecks.KernelSpor.CF24.sg2M
#ks_perm CertificateChecks.KernelSpor.CF24.SG3 11 CertificateChecks.KernelSpor.CF24.sg3M
#ks_perm CertificateChecks.KernelSpor.CF24.SG4 11 CertificateChecks.KernelSpor.CF24.sg4M
#ks_perm CertificateChecks.KernelSpor.CF24.SG5 11 CertificateChecks.KernelSpor.CF24.sg5M
#ks_perm CertificateChecks.KernelSpor.CF24.SG6 11 CertificateChecks.KernelSpor.CF24.sg6M
#ks_perm CertificateChecks.KernelSpor.CF24.SGI0 11 CertificateChecks.KernelSpor.CF24.sgi0M
#ks_perm CertificateChecks.KernelSpor.CF24.SGI1 11 CertificateChecks.KernelSpor.CF24.sgi1M
#ks_perm CertificateChecks.KernelSpor.CF24.SGI2 11 CertificateChecks.KernelSpor.CF24.sgi2M
#ks_perm CertificateChecks.KernelSpor.CF24.SGI3 11 CertificateChecks.KernelSpor.CF24.sgi3M
#ks_perm CertificateChecks.KernelSpor.CF24.SGI4 11 CertificateChecks.KernelSpor.CF24.sgi4M
#ks_perm CertificateChecks.KernelSpor.CF24.SGI5 11 CertificateChecks.KernelSpor.CF24.sgi5M
#ks_perm CertificateChecks.KernelSpor.CF24.SGI6 11 CertificateChecks.KernelSpor.CF24.sgi6M
#ks_perm CertificateChecks.KernelSpor.CF24.L0 11 CertificateChecks.KernelSpor.CF24.l0M
#ks_perm CertificateChecks.KernelSpor.CF24.L1 11 CertificateChecks.KernelSpor.CF24.l1M
#ks_perm CertificateChecks.KernelSpor.CF24.L2 11 CertificateChecks.KernelSpor.CF24.l2M
#ks_perm CertificateChecks.KernelSpor.CF24.L3 11 CertificateChecks.KernelSpor.CF24.l3M
#ks_perm CertificateChecks.KernelSpor.CF24.L4 11 CertificateChecks.KernelSpor.CF24.l4M
#ks_perm CertificateChecks.KernelSpor.CF24.LI0 11 CertificateChecks.KernelSpor.CF24.li0M
#ks_perm CertificateChecks.KernelSpor.CF24.LI1 11 CertificateChecks.KernelSpor.CF24.li1M
#ks_perm CertificateChecks.KernelSpor.CF24.LI2 11 CertificateChecks.KernelSpor.CF24.li2M
#ks_perm CertificateChecks.KernelSpor.CF24.LI3 11 CertificateChecks.KernelSpor.CF24.li3M
#ks_perm CertificateChecks.KernelSpor.CF24.LI4 11 CertificateChecks.KernelSpor.CF24.li4M
#ks_perm CertificateChecks.KernelSpor.CF24.XK 11 CertificateChecks.KernelSpor.CF24.xM
#ks_perm CertificateChecks.KernelSpor.CF24.YK 11 CertificateChecks.KernelSpor.CF24.yM
#ks_perm CertificateChecks.KernelSpor.CF24.OM 1 CertificateChecks.KernelSpor.CF24.omM

#lc_words CertificateChecks.KernelSpor.CF24.IW CFSG.Sporadic.Bridge.SuzGPL.Native.imgText

end
