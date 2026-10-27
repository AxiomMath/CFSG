module

public import Certificates.Kernel.Q8Wit.J2Sift
public import Certificates.Kernel.Q8Wit.L34Glue
public import Certificates.Kernel.Q8Wit.L34Ext
public import CFSG.Certificates.Kernel.Q8WitL34Sound
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Kernel.Q8Wit.J2Checks

public section

namespace CertificateChecks.KernelQ8W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.Q8Wit CFSG.KC.E81K CFSG.KC.L34K Certificates.TwinPerpSmSp1
open CFSG.Monster.B.Co2 (allLt_iff)

theorem j2InP_true : CFSG.Monster.B.Co2.Native.allLt j2Wit.xg.size (fun l =>
    CFSG.ComponentClassification.J2Cover.inP j2Wit.xg[l]!) = true := by
  have bX := binds_of_check J2.bindXG
  rw [allLt_iff, bX.1]
  intro l hl
  have h := allN_spec J2.sift l hl
  unfold J2.inPK at h
  simp only [Bool.and_eq_true] at h
  exact CertificateChecks.KernelJ2Cover.inP_of (bX.2 l hl) h.1.1 h.1.2 h.2

theorem l34Pts : (CFSG.CGT.PushingUpLit.SolKNA.R4.Check.qCert l34Wit.syl).pts =
      Array.ofFn (n := L34.Q.N) (fun i => unpack 42 6 (L34.Q.T i.val)) ∧
    ∀ i < L34.Q.N, (CFSG.CGT.PushingUpLit.SolKNA.R4.Check.qCert l34Wit.syl).pts[i]! =
      unpack 42 6 (L34.Q.T i) ∧ permB 42 6 (L34.Q.T i) = true := by
  have bP := binds_of_check L34.bindPG
  have hq := words L34.hw bP.2 (allN_spec L34.permPG) L34.wordsQ L34.lettersQ
  have hk : ∀ p ∈ l34Wit.syl.qKeys, p < 42 := by decide
  have h := pin_facts L34.pinQ (fuel := l34Wit.syl.qFuel) hq.1 hq.2 hk (by decide)
  exact ⟨h.1, h.2.2⟩

theorem l34Sq_true : l34SqCheck () = true := by
  unfold l34SqCheck
  rw [CertificateChecks.KernelLC.L34Cert.hS.1]
  obtain ⟨e, hp⟩ := l34Pts
  rw [e]
  refine q8SqIn_of L34.hw (by rw [Array.size_ofFn]) (fun i hi => ?_)
    (fun i hi => pp_of_permB L34.hw (hp i hi).2) L34.tabs L34.sqIn
  rw [← e]
  exact (hp i hi).1

theorem l34Cent_true : l34CentCheck () = true := by
  unfold l34CentCheck
  dsimp only
  rw [CertificateChecks.KernelLC.L34Cert.hR.1, CertificateChecks.KernelLC.L34Cert.hS.1,
    CertificateChecks.KernelLC.L34Cert.cent1]
  refine cent_of L34.hw CertificateChecks.KernelLC.L34Cert.pinR.canon (allN_spec L34.c1Canon)
    fun k hk => ?_
  have hs : k / 20160 < 12 := by omega
  have h := allN_spec (L34.centAll (k / 20160) hs) (k % 20160) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 20160 (k / 20160)) (k % 20160) = k := Nat.div_add_mod k 20160
  rw [e] at h
  exact h

end CertificateChecks.KernelQ8W

end
