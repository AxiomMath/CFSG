module

public import Certificates.Kernel.HatM.Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.NatBuckets

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHatM

open CFSG.KC.HatChkK
open CFSG.KC.Misc.ArrEnum (arrBind)
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Quasithin.H13.Ch4.HatChk CFSG.Quasithin.H13.Ch4.HatM
open CFSG.Sporadic.Mathieu

theorem pairS1 : (List.range 512).all (fun j => fpfPairK 24 5 9 ES1.G (RA 0) (ES1.T j)) = true := by
  quickRfl

@[expose] noncomputable def memPB (i : ℕ) : Bool :=
  CFSG.KC.NatBuckets.memB (CFSG.KC.NatBuckets.bucketsOf ((List.range 1024).map EP2.T)) (EP1.T i)

@[expose] noncomputable def memIB (i : ℕ) : Bool :=
  if i < 1024 then memPB i else CFSG.KC.HatChkK.memL 24 ps24 cP2.pts cP1.pts[i]!

theorem memP_eqB : memP = memPB := by
  funext i
  simp only [memP, memPB, ← CFSG.KC.NatBuckets.memN_eq_memB, CFSG.KC.NatBuckets.memN, List.any_map,
    Function.comp_def]

theorem memI_eqB : memI = memIB := by
  funext i
  unfold memI memIB
  rw [memP_eqB]

theorem greedy : arrBind (greedyF 1024 memI cmI) 1024 6 (CL 0) = true := by
  rw [memI_eqB]
  quickRfl

theorem cover : coverF 1024 63 memC clsC cmI = true := by quickRfl

end CertificateChecks.KernelHatM

end
