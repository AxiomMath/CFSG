module

public import Certificates.Kernel.Sporadic.OddCore.S16J3K27810
public import Certificates.Kernel.SporSch.J3K426.Sift
public import CFSG.Certificates.Kernel.Spor.RawOrbOutSound
public import CFSG.Sporadic.Schreier.PairJ3Order
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue

public section

namespace CertificateChecks.KernelSpor.S16J3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.Certificates
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairJ3 CFSG.Sporadic.SmallOddCore
open CFSG.Monster.B.Co2 CertificateChecks.KernelSporSch

theorem gen_eq : Orb.Gen 6156 j3StrongArrs 2 = j3P := by
  unfold Orb.Gen j3P
  rw [PJ3Check.range_two (fun j => permOfArr 6156 j3StrongArrs[j]!)]
  rfl


theorem sift_false_of_out {X XI : Nat} {iw : List Int} (hc : cK X = true) (hi : iK X XI = true)
    (h : outJ3 iw X = true) : j3Sift (tabT (unpack 6156 13 X)) = false := by
  cases hs : j3Sift (tabT (unpack 6156 13 X))
  · rfl
  · exfalso
    have hr := (rep_permOfArr (invEqK_sound hi).2).1
    unfold j3Sift at hs
    rw [natArr_tabT hc] at hs
    have hm := (siftA_iff_mem_originalSubgroup j3ChainArrays (by norm_num)
      PJ3Check.facts.1.1 hr).1 hs
    rw [← j3P_eq_original, ← gen_eq] at hm
    exact Orb.not_mem_Gen_of_outK J3KT.hd PJ3Check.binds PJ3Check.perm PJ3.ho (by norm_num)
      PJ3Check.card_le (by norm_num) (Orb.prep_of_rep hr) h hm

theorem sift_r : j3Sift (tabT (unpack 6156 13 rK)) = false := by
  have h := k_rout
  simp only [bAnd_iff] at h
  exact sift_false_of_out h.1 h.2.1 h.2.2

end CertificateChecks.KernelSpor.S16J3

end
