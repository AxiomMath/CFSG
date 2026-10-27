module

public import Certificates.Kernel.LocalComp.L34Ord.Chk
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34FixPowSound
public import CFSG.Certificates.Kernel.L34ScanSound
public import Certificates.Data.CFSGNative.PSL3Four.L34Ord
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Ord

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34FixPow
open CFSG.KC.L34Scan CFSG.KC.L34W CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB)

theorem ordSl_all : ∀ s < 15, scanSl ordPt CertificateChecks.KernelLC.L34S.T 1344 s = true := by
  intro s hs
  have hc : ordSl (s / 5) = true := by
    rcases (by omega : s / 5 = 0 ∨ s / 5 = 1 ∨ s / 5 = 2) with h | h | h <;> rw [h]
    exacts [k85c0, k85c1, k85c2]
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hc (s % 5) (Nat.mod_lt _ (by decide))
  beta_reduce at h
  have e : Nat.add (Nat.mul 5 (s / 5)) (s % 5) = s := Nat.div_add_mod s 5
  rwa [e] at h

theorem ordAll : ∀ i < 20160, ordPt (CertificateChecks.KernelLC.L34S.T i) = true :=
  scanSl_spec (L := 1344) (K := 15) (by decide) (by decide) ordSl_all

theorem ord_sound {x : Nat} (hx : Cn x) (h : ordPt x = true) :
    ((!(powTab 42 (unpack 42 6 x) 15 == idTab 42) || powTab 42 (unpack 42 6 x) 3 == idTab 42 ||
        powTab 42 (unpack 42 6 x) 5 == idTab 42) &&
      (!(powTab 42 (unpack 42 6 x) 21 == idTab 42) || powTab 42 (unpack 42 6 x) 3 == idTab 42 ||
        powTab 42 (unpack 42 6 x) 7 == idTab 42)) = true := by
  simp only [fixPow_eq hx]
  unfold ordPt at h
  revert h
  generalize fixPow x 3 = a
  generalize fixPow x 5 = b
  generalize fixPow x 7 = c
  generalize fixPow x 15 = d
  generalize fixPow x 21 = f
  cases a <;> cases b <;> cases c <;> cases d <;> cases f <;> decide

theorem ord_true : l34OrdCheck (enumBFS 42 gensS 20160).tabs = true := by
  unfold l34OrdCheck
  rw [hS.1, CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro i hi
  rw [pts_get' hi]
  exact ord_sound (pinS.canon i hi) (ordAll i hi)

end CertificateChecks.KernelLC.L34Ord

end
