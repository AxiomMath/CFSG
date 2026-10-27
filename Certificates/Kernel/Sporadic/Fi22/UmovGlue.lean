module

public import Certificates.Kernel.Sporadic.Fi22.Umov
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Sporadic.Fi22.C2068Base

public section

namespace CertificateChecks.KernelSpor.Fi22Um

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.HypOne.Fi22
open CFSG.Sporadic.SmallOddCore.Native

theorem umovTbl_eq {k : Nat} (hk : k < 18) :
    fi22UmovTbl k = tabT (unpack 3510 12 (F k)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound all (by norm_num) k hk
  rw [← eq] at h
  rw [← h, tabT_natArr]
  rfl

theorem tT_eq {k : Nat} (hk : k < 6) : tT k = tabT (unpack 3510 12 (Fi22ExtT.L (21 + k))) := by
  rw [← Fi22E2067.ext_eq (by omega)]
  rfl

theorem umovWitOK_of {L T T' : Nat} (h : umovK L T T' = true) :
    umovWitOK 3510 siftP (tabT (unpack 3510 12 L)) (tabT (unpack 3510 12 T))
      (tabT (unpack 3510 12 T')) = true := by
  simp only [umovK, bAnd_iff, strictB_eq''] at h
  obtain ⟨hL, hLi, pL, sL, hT, pT, hT', pT', e⟩ := h
  unfold umovWitOK
  rw [invT_unpack (by norm_num) pL, conjT_unpack hL hLi hT,
    commTT_unpack (canonK_pcomp (canonK_pcomp hL hT) hLi) hT', permOK_unpack hL pL,
    permOK_unpack hT pT, permOK_unpack hT' pT', invOK_unpack hL hLi pL]
  have hs : siftP (tabT (unpack 3510 12 L)) = true := by
    unfold siftP
    rw [natArr_tabT hL, Fi22LabA.fi22InP_eq rfl hL]
    exact sL
  rw [hs]
  simpa [Fi22X.c] using e

theorem fi22UmovData_true : fi22UmovData = true := by
  unfold fi22UmovData
  simp only [List.all_eq_true, List.mem_range]
  intro i hi j hj
  rw [umovTbl_eq (by omega), tT_eq (by omega), tT_eq hj]
  exact umovWitOK_of (allN_spec (allN_spec umAll i hi) j hj)

end CertificateChecks.KernelSpor.Fi22Um

end
