module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.B3S3.GenL
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.RankThree.Native.Fi22FiveArrays
public meta import CFSG.RankThree.Native.Fi22FiveArrays
public meta import Certificates.Kernel.B3S3.Gen
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import Std.Data.HashMap

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSpor.Fv8124

open CFSG.RankThree.Native

meta def dGens0 : Array (Array Nat) := fi22FiveDGenArrs 0

end CertificateChecks.KernelSpor.Fv8124

end

set_option Elab.async false

#ks_chars CertificateChecks.KernelSpor.Fv8124T CFSG.RankThree.Native.fi22FiveHex
#kmisc_hexflat CertificateChecks.KernelSpor.Fv8124T CFSG.RankThree.Native.fi22FiveHex 3 3510 12 8
#kb3_enum_l CertificateChecks.KernelSpor.Fv8124E CertificateChecks.KernelSpor.Fv8124.dGens0
  CFSG.Monster.B.Fischer.fi22BaseArr 3510 12
