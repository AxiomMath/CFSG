module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalComp.McLCent
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Data.McLCls
meta import Certificates.Data.McLCls
meta import CFSG.Sporadic.SmallOddCore.McLData

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMcLCls.CT CFSG.SectionRank.QTK.Insp443.McLCls.mclClsHex
#kmisc_hexflat CertificateChecks.KernelMcLCls.CT CFSG.SectionRank.QTK.Insp443.McLCls.mclClsHex
  3 275 9 9

namespace CertificateChecks.KernelMcLCls

meta def invM (a : Array Nat) : Array Nat :=
  (List.range 275).foldl (fun r i => r.set! a[i]! i) (Array.replicate 275 0)

meta def natM (T : Array UInt32) : Array Nat := T.map UInt32.toNat

meta def clsInvM : Array (Array Nat) :=
  (List.range 9).toArray.map fun k => invM (natM (CFSG.SectionRank.QTK.Insp443.McLCls.clsTbl k))

meta def centInvM : Array (Array Nat) :=
  #[0, 4, 5, 6].map fun k => invM (natM (CFSG.Sporadic.SmallOddCore.mclCentTbl k))

end CertificateChecks.KernelMcLCls

#kmisc_packarrs CertificateChecks.KernelMcLCls.CI CertificateChecks.KernelMcLCls.clsInvM 9
#kmisc_packarrs CertificateChecks.KernelMcLCls.MI CertificateChecks.KernelMcLCls.centInvM 9

namespace CertificateChecks.KernelMcLCls

open CFSG.KC.Misc.HexFlat CFSG.KS.Raw CFSG.SectionRank.QTK.Insp443.McLCls

theorem clsTbl_eq {k : Nat} (hk : k < 9) :
    CFSG.Sporadic.SmallOddCore.Native.natArr (clsTbl k) = unpack 275 9 (CT.F k) := by
  rw [clsTbl, CT.eq]
  exact hexT_sound CT.all (by norm_num) k hk

end CertificateChecks.KernelMcLCls

end
