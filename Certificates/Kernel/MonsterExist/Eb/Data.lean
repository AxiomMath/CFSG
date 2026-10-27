module

public import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CertificateChecks.MonsterExist.Eb

@[expose] def CLText : String := include_str "eb_cl.hex"

@[expose] def CPText : String := include_str "eb_cp.hex"

@[expose] def CEText : String := include_str "eb_ce.hex"

@[expose] def SHText : String := include_str "eb_sh.hex"

@[expose] noncomputable def CL : Nat := by
  hex_nat CLText 1663 15936435143419388878

@[expose] noncomputable def CP : Nat := by
  hex_nat CPText 1023 9989620752086017562

@[expose] noncomputable def CE : Nat := by
  hex_nat CEText 12288 2314965631575361322

@[expose] noncomputable def SH : Nat := by
  hex_nat SHText 780 1741355820855568439

end CertificateChecks.MonsterExist.Eb

end
