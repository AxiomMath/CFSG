module

public import CFSG.Certificates.Kernel.SmithEK.QSound
public import Certificates.Kernel.SmithEK.ChecksQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.LargeExtraspecial.SMod20

theorem qpins : QPins wd.W wd.M pb.P cs.L where
  w i hi := by
    rw [← wtArr_wd hi, CFSG.LargeExtraspecial.SMod20.wtArr_get hi]
  m i hi := (wMask_eq_wd hi).symm
  p i hi a ha := by
    have hm : maskArr[i]! = wMask i := by simp [maskArr, getElem!_pos, hi]
    have hu : uPts[a]! = pts.L.getD a 0 := by
      rw [uPts_eq, List.getD_eq_getElem?_getD, getElem!_pos _ a (by simpa [pts_length] using ha)]
      simp [ha, pts_length]
    rw [pb_get hi, testBit_ptBits, inPlane, hm, hu, pts_length]
    simp [ha]
  c k hk := by rw [← tvArr_cs k, CFSG.LargeExtraspecial.SMod20.tvArr_get hk]
  wl := wd_len
  ml := wdM_len

theorem qa0 :
    ∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
      (∀ s, ∃ p : Fin 693, p ∈ planeSet 0 ∧ ∃ k : Fin 891, ¬ Opp 0 k ∧
        v s = tvLin p.val (wtV k.val) + wtV k.val) ∧
      ∀ j : Fin 891, wtV j.val ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW 0 j.val = true :=
  qa_sound qpins c21267qa_0

theorem cv0 :
    ∀ v : V, (∀ p ∈ planeSet 0, tvLin p.val v = v) ↔ v = 0 ∨ v = wtV 0 :=
  cv_sound qpins c21267cv_0

end CertificateChecks.KernelSmithEK
