module

public import Certificates.Kernel.J3Local.Check
public import CFSG.Certificates.Kernel.J3LocalSound
public import Certificates.Kernel.Sporadic.J3K.Final

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3L

open CFSG.KC.J3Loc CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
open CertificateChecks.KernelSpor.J3K

theorem j3A : (ops2 80).decode NativeSporadic.J3Seed1 = CFSG.KC.Co1F2.unpackR 80 JA.M := by
  rw [JA.eq]
  exact CFSG.KC.Co1F2.bind_sound JA.bind

theorem j3B : (ops2 80).decode NativeSporadic.J3Seed2 = CFSG.KC.Co1F2.unpackR 80 JB.M := by
  rw [JB.eq]
  exact CFSG.KC.Co1F2.bind_sound JB.bind

theorem pts_eq : (CFSG.Sporadic.J3.Native.j3Data ()).pts = PTS := by
  unfold CFSG.Sporadic.J3.Native.Data.pts CFSG.Sporadic.J3.Native.Data.colsA
    CFSG.Sporadic.J3.Native.Data.colsB
  have hv : (CFSG.Sporadic.J3.Native.j3Data ()).v0 = 16561281922307987041 := rfl
  have hn : (CFSG.Sporadic.J3.Native.j3Data ()).n = 20520 := rfl
  rw [rowsA_D, rowsB_D, colsA_eq, colsB_eq, hv, hn]
  exact orb_eq.1

theorem j3_check_K : j3Check NativeSporadic.J3Seed1 NativeSporadic.J3Seed2
    CFSG.Sporadic.J3.Native.j3Data.pts CFSG.Sporadic.J3.Native.j3Data.n
    CFSG.RankThree.Asc83Table.J3.j3Cert = true := by
  have hn : (CFSG.Sporadic.J3.Native.j3Data ()).n = 20520 := rfl
  rw [hn]
  exact j3Check_of_K j3A j3B (by norm_num) (by norm_num)
    (fun i hi => by rw [pts_eq]; exact pts_get hi) (fun i hi => (pt_spec hi).1) full_K

end CertificateChecks.KernelJ3L

end
