module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Recognition.McLASData
public import CFSG.Sporadic.Recognition.LyonsAS44McLData
public import CFSG.Sporadic.Recognition.McLASThreeLocalData
public import CFSG.Sporadic.Recognition.LyonsLocalMcLInputs
meta import CFSG.Sporadic.Recognition.McLASData
meta import CFSG.Sporadic.Recognition.LyonsAS44McLData
meta import CFSG.Sporadic.Recognition.McLASThreeLocalData
meta import CFSG.Sporadic.Recognition.LyonsLocalMcLInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMcLAS.TT CFSG.Sporadic.Recognition.McLAS.threeHex
#kmisc_hexflat CertificateChecks.KernelMcLAS.TT CFSG.Sporadic.Recognition.McLAS.threeHex 3 275 9 11
#ks_chars CertificateChecks.KernelMcLAS.NT CFSG.Sporadic.Recognition.McLAS.nrmHex
#kmisc_hexflat CertificateChecks.KernelMcLAS.NT CFSG.Sporadic.Recognition.McLAS.nrmHex 3 275 9 22
#ks_chars CertificateChecks.KernelMcLAS.TL CFSG.Sporadic.Recognition.McLAS.tlHex
#kmisc_hexflat CertificateChecks.KernelMcLAS.TL CFSG.Sporadic.Recognition.McLAS.tlHex 3 275 9 15
#ks_chars CertificateChecks.KernelMcLAS.PT CFSG.Sporadic.Recognition.McLAS.pairHex
#kmisc_hexflat CertificateChecks.KernelMcLAS.PT CFSG.Sporadic.Recognition.McLAS.pairHex 3 275 9 1

namespace CertificateChecks.KernelMcLAS

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native

meta def invsM (f : Nat → Table) (N : Nat) : Array (Array Nat) :=
  (List.range N).toArray.map fun k => CFSG.Monster.B.Co2.Native.invCand 275 (natArr (f k))

meta def ttInvM : Array (Array Nat) := invsM threeTbl 11
meta def ntInvM : Array (Array Nat) := invsM nrmTbl 22
meta def tlInvM : Array (Array Nat) := invsM tlTbl 15
meta def ptInvM : Array (Array Nat) := invsM (fun _ => pairTbl) 1

end CertificateChecks.KernelMcLAS

#kmisc_packarrs CertificateChecks.KernelMcLAS.TTI CertificateChecks.KernelMcLAS.ttInvM 9
#kmisc_packarrs CertificateChecks.KernelMcLAS.NTI CertificateChecks.KernelMcLAS.ntInvM 9
#kmisc_packarrs CertificateChecks.KernelMcLAS.TLI CertificateChecks.KernelMcLAS.tlInvM 9
#kmisc_packarrs CertificateChecks.KernelMcLAS.PTI CertificateChecks.KernelMcLAS.ptInvM 9

namespace CertificateChecks.KernelMcLAS

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore.Native CFSG.KS.Raw CFSG.KC.Enum
open CFSG.KS CFSG.KS.Prim

theorem perms : bAnd(allN 11 (fun k => invEqK 275 9 (mask 9) (275 * 9) (TT.F k) (TTI k)),
    bAnd(allN 22 (fun k => invEqK 275 9 (mask 9) (275 * 9) (NT.F k) (NTI k)),
    bAnd(allN 15 (fun k => invEqK 275 9 (mask 9) (275 * 9) (TL.F k) (TLI k)),
      invEqK 275 9 (mask 9) (275 * 9) (PT.F 0) (PTI 0)))) = true := by
  quickRfl

theorem threeTbl_eq {k : Nat} (hk : k < 11) : natArr (threeTbl k) = unpack 275 9 (TT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound TT.all (by norm_num) k hk
  rw [← TT.eq] at h
  exact h

theorem nrmTbl_eq {k : Nat} (hk : k < 22) : natArr (nrmTbl k) = unpack 275 9 (NT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound NT.all (by norm_num) k hk
  rw [← NT.eq] at h
  exact h

theorem tlTbl_eq {k : Nat} (hk : k < 15) : natArr (tlTbl k) = unpack 275 9 (TL.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound TL.all (by norm_num) k hk
  rw [← TL.eq] at h
  exact h

theorem pairTbl_eq : natArr pairTbl = unpack 275 9 (PT.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound PT.all (by norm_num) 0 (by norm_num)
  rw [← PT.eq] at h
  exact h

end CertificateChecks.KernelMcLAS

end
