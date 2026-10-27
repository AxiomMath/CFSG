module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.JoinSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.SmallOddCore.J3DataInputs
meta import CFSG.Sporadic.SmallOddCore.J3DataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.J3CentT CFSG.Sporadic.SmallOddCore.j3CentHex

#kmisc_hexflat CertificateChecks.KernelSpor.J3CentT CFSG.Sporadic.SmallOddCore.j3CentHex
  4 513 13 372

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def j3CentM : Array (Array Nat) :=
  (List.range 31).toArray.map fun k => natArr (j3CentTbl k)

meta def j3CentInvM : Array (Array Nat) :=
  j3CentM.map (CFSG.Monster.B.Co2.Native.invCand 6156)

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.J3CentP CertificateChecks.KernelSpor.OddCore.j3CentM 13

#kmisc_packarrs CertificateChecks.KernelSpor.J3CentI CertificateChecks.KernelSpor.OddCore.j3CentInvM 13

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.KS.Raw CFSG.KC.Enum
open CFSG.KS CFSG.KS.Prim CFSG.KS.Join

theorem j3_join : joinK 12 (13 * 513) J3CentT.F J3CentP 31 = true := by
  quickRfl

@[expose] noncomputable def j3Perm (k : Nat) : Bool :=
  invEqK 6156 13 (mask 13) (6156 * 13) (J3CentP k) (J3CentI k)

theorem j3_perms0 : allBlk 0 j3Perm 8 = true := by
  quickRfl

theorem j3_perms1 : allBlk 8 j3Perm 8 = true := by
  quickRfl

theorem j3_perms2 : allBlk 16 j3Perm 8 = true := by
  quickRfl

theorem j3_perms3 : allBlk 24 j3Perm 7 = true := by
  quickRfl

theorem j3_perm {k : Nat} (hk : k < 31) : j3Perm k = true := by
  rcases Nat.lt_or_ge k 8 with h0 | h0
  · simpa using allBlk_spec j3_perms0 k h0
  rcases Nat.lt_or_ge k 16 with h1 | h1
  · simpa [Nat.add_sub_cancel' h0] using allBlk_spec j3_perms1 (k - 8) (by omega)
  rcases Nat.lt_or_ge k 24 with h2 | h2
  · simpa [Nat.add_sub_cancel' h1] using allBlk_spec j3_perms2 (k - 16) (by omega)
  · simpa [Nat.add_sub_cancel' h2] using allBlk_spec j3_perms3 (k - 24) (by omega)

theorem j3CentTbl_eq {k : Nat} (hk : k < 31) :
    natArr (j3CentTbl k) = unpack 6156 13 (J3CentP k) := by
  have h := hexT_join_sound (d := 4) (n₀ := 513) (w := 13) (c := 12) (N := 31) J3CentT.all j3_join
    (by norm_num) k hk
  rw [← J3CentT.eq] at h
  exact h

theorem j3_permOK_all : (List.range 31).all
    (fun k => CFSG.Sporadic.SmallOddCore.permOK 6156 (j3CentTbl k)) = true := by
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < 31 := List.mem_range.1 hk
  obtain ⟨h1, h2⟩ := invEqK_sound (j3_perm hk')
  unfold CFSG.Sporadic.SmallOddCore.permOK
  rw [j3CentTbl_eq hk', h1]
  exact h2

end CertificateChecks.KernelSpor.OddCore

end
