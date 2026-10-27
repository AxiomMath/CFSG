module

public import Certificates.Kernel.SmithEK.VRowsA
public import Certificates.Kernel.SmithEK.VRowsB
public import Certificates.Kernel.SmithEK.ChkG
public import CFSG.Certificates.Kernel.SmithEK.VSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

#kc_forall_tree vrows_all (fun c => fixChunkK tp.C wd.W pb.P pts.L (27 * c) 27 = true) 33
  CertificateChecks.KernelSmithEK.c21260fix_

theorem fix_iff {a i : Nat} (ha : a < 693) (hi : i < 891) :
    applyCols tvArr[a]! wtArr[i]! = wtArr[i]! ↔ inPlane i a = true := by
  have hc : i / 27 < 33 := by omega
  have h1 : 27 * (i / 27) ≤ i := by omega
  have h2 : i < 27 * (i / 27) + 27 := by omega
  obtain ⟨-, hr⟩ := fixChunkK_sound (vrows_all (i / 27) hc) h1 h2
  have e := fixRowK_sound _ _ _ _ hr a (by rw [pts_length]; exact ha)
  rw [wtArr_wd hi, ← lane_tv ha, inPlane_eq uPts_eq pts_length (fun _ hk => pb_get hk) hi ha]
  exact e

theorem wt_lt {i : Nat} (hi : i < 891) : wtArr[i]! < 2 ^ 20 := by
  have hc : i / 27 < 33 := by omega
  have h1 : 27 * (i / 27) ≤ i := by omega
  have h2 : i < 27 * (i / 27) + 27 := by omega
  rw [wtArr_wd hi]
  exact (fixChunkK_sound (vrows_all (i / 27) hc) h1 h2).1

theorem chkTW_eq : chkTW = true := by
  have hr := rows_of c21260conj
  obtain ⟨-, hc⟩ := bounds_of c21260conj
  refine chkTW_of chkT_eq (fun a ha i hi => fix_iff ha hi) (fun i hi => wt_lt hi)
    (fun k hk a ha => ?_) (fun k hk x hx => ?_)
  · obtain ⟨e1, e2⟩ := ptImg_R k hk a ha
    obtain ⟨-, e3⟩ := (hr k hk).2 a ha
    refine ⟨by rw [e1]; exact e2, fun x => ?_⟩
    rw [e1]
    simp only [tvArr_cs, applyCols_toArray]
    exact conj_of_cols (hc k hk).1 (hc _ e2).1 e3 x
  · simp only [tvArr_cs, applyCols_toArray]
    exact invol_of_cols (hc k hk).1 (hr k hk).1 hx

end CertificateChecks.KernelSmithEK
