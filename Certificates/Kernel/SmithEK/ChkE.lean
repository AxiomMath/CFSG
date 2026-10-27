module

public import Certificates.Kernel.SmithEK.EChk
public import CFSG.Certificates.Kernel.SmithEK.ESound
public import CFSG.Certificates.Kernel.SmithEK.TSound
public import Certificates.Kernel.SmithEK.Span

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem cs_length : cs.L.length = 693 := by
  rw [← cs_ok, List.length_map, pts_length]

theorem tvArr_cs (k : Nat) : tvArr[k]! = (cs.L.getD k []).toArray := by
  by_cases hk : k < 693
  · have hk' : k < pts.L.length := by rw [pts_length]; exact hk
    rw [tvArr_get hk, tvCols_eq, ← tvW_cTabQ, ← cT_eq, ← cs_ok]
    simp [List.getD_eq_getElem?_getD, hk']
  · have hs : tvArr.size = 693 := Array.size_ofFn
    rw [getElem!_neg tvArr k (by omega), List.getD_eq_default _ _ (by rw [cs_length]; omega)]
    rfl

theorem chkC8Pts_eq : chkC8Pts = true :=
  chkC8Pts_of tvArr_cs (by rw [c8c_Q]; exact c21265pts)

theorem chkC8Fix_eq : chkC8Fix = true := chkC8Fix_of tvArr_cs c21265fix

theorem chkC8Restr_eq : chkC8Restr = true :=
  chkC8Restr_of tvArr_cs cs_length (by rw [c8c_Q]; exact c21265restr)

theorem chkC8Irr_eq : chkC8Irr = true := chkC8Irr_of tvArr_cs (by rw [c8c_Q]; exact c21265irr)

theorem chkRigid_eq : chkRigid = true := by
  have h := c21265fix
  unfold c8FixK at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  exact chkRigid_of tvArr_cs (fun m hm => (h.1 m hm).1) (by rw [c8c_S]; exact c21265rig)
    c21265rig2

end CertificateChecks.KernelSmithEK
