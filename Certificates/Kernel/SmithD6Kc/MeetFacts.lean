module

public import Certificates.Kernel.SmithD6Kc.Facts
public import CFSG.Certificates.Kernel.SmithD6MeetSound

public section

namespace CertificateChecks.SmithD6Kc

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6

theorem d6PB_eq {j : ℕ} (hj : j < 75735) :
    d6PB j = J.pbC.flatten.getD j #[] ∧ d6PP j = J.ppC.flatten.getD j #[] := by
  obtain ⟨e1, e2, -⟩ := pb_flat_getD hj
  unfold d6PB d6PP
  rw [nthA_eq, nthA_eq, nthB_eq, nthB_eq]
  exact ⟨e1.symm, e2.symm⟩

theorem meetCnt_eq_d6MeetK (hpb : ∀ i < 75735, pbArr[i]! = J.pbC.flatten.getD i #[])
    (hpp : ∀ i < 75735, ppArr[i]! = J.ppC.flatten.getD i #[]) {i j : ℕ} (hi : i < 75735)
    (hj : j < 75735) : meetCnt i j = d6MeetK i j := by
  unfold meetCnt d6MeetK
  rw [hpb i hi, hpb j hj, hpp j hj, (d6PB_eq hi).1, (d6PB_eq hj).1, (d6PB_eq hj).2]
  obtain ⟨si, -⟩ := pb_size hi
  obtain ⟨sj, sp⟩ := pb_size hj
  rcases hBi : J.pbC.flatten.getD i #[] with ⟨bi⟩
  rcases hBj : J.pbC.flatten.getD j #[] with ⟨bj⟩
  rcases hPj : J.ppC.flatten.getD j #[] with ⟨pj⟩
  rw [hBi] at si
  rw [hBj] at sj
  rw [hPj] at sp
  have li : bi.length = 6 := by simpa using si
  have lj : bj.length = 6 := by simpa using sj
  have lp : pj.length = 6 := by simpa using sp
  change _ = kcMeetN bi bj pj
  rw [kcMeetN_eq li (by rw [lj, lp])]
  congr 2
  funext d
  rw [memR_eq_kcMem lj lp, xorComb_eq_selF li]

end CertificateChecks.SmithD6Kc

end
