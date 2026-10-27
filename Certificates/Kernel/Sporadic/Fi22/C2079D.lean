module

public import Certificates.Kernel.Sporadic.Fi22.C2079A
public import CFSG.Certificates.Kernel.Spor.OrbTreeKProof
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fo22C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermTool CFSG.KS.OrbTree
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor

theorem tK3 : treeK 1575 11 11 4 Fo22P3.S Fo22T.TOrd3.F Fo22T.TPa3.F Fo22T.TGe3.F = true := by
  quickRfl
theorem tK4 : treeK 63 7 7 4 Fo22P4.S Fo22T.TOrd4.F Fo22T.TPa4.F Fo22T.TGe4.F = true := by
  quickRfl
theorem sK3 : subK 1575 11 11 4 11 7 Fo22P3.S (fun c => fo22Start3[c]!) Fo22T.Lab3.F Fo22T.Ord3.F
    Fo22T.TPar3.F Fo22T.TGen3.F = true := by quickRfl
theorem sK4 : subK 63 7 7 4 11 3 Fo22P4.S (fun c => fo22Start4[c]!) Fo22T.Lab4.F Fo22T.Ord4.F
    Fo22T.TPar4.F Fo22T.TGen4.F = true := by quickRfl
theorem oK4 : orbitK 3510 63 7 12 Fo22N4.S Fo22P4.S Fo22T.O63.F = true := by quickRfl

theorem tree3 : fo22TreeOK 1575 fo22P3Strong fo22TOrd3 fo22TPa3 fo22TGe3 = true := by
  rw [p3S, Fo22T.tord3_eq, Fo22T.tpa3_eq, Fo22T.tge3_eq]
  exact treeK_sound (by norm_num) tK3

theorem tree4 : fo22TreeOK 63 fo22P4Strong fo22TOrd4 fo22TPa4 fo22TGe4 = true := by
  rw [p4S, Fo22T.tord4_eq, Fo22T.tpa4_eq, Fo22T.tge4_eq]
  exact treeK_sound (by norm_num) tK4

theorem sub3 : fo22SubOK 1575 fo22P3Strong fo22Lab3 fo22Ord3 fo22TPar3 fo22TGen3 fo22Start3 7 =
    true := by
  rw [p3S, Fo22T.lab3_eq, Fo22T.ord3_eq, Fo22T.tpar3_eq, Fo22T.tgen3_eq]
  exact subK_sound (by norm_num) rfl sK3

theorem sub4 : fo22SubOK 63 fo22P4Strong fo22Lab4 fo22Ord4 fo22TPar4 fo22TGen4 fo22Start4 3 =
    true := by
  rw [p4S, Fo22T.lab4_eq, Fo22T.ord4_eq, Fo22T.tpar4_eq, Fo22T.tgen4_eq]
  exact subK_sound (by norm_num) rfl sK4

theorem orbit4 : fo22OrbitOK fo22N4Strong fo22O63 fo22P4Strong 63 = true := by
  rw [n4S, p4S, Fo22T.o63_eq]
  exact orbitK_sound (by norm_num) (by norm_num) (by norm_num) (by norm_num) oK4

theorem powA_unpack {n w p : Nat} (hid : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hidA : idK n w (mask w) = true) (hp : canonK n w (mask w) (n * w) p = true) :
    ∀ e, powA n (unpack n w p) e = unpack n w (powK n w p e)
  | 0 => by
    rw [powA, ← idK_sound hidA]
    rfl
  | e + 1 => by
    rw [powA, powA_unpack hid hidA hp e, compA_unpack hp (canonK_powK hid hp e)]
    rfl

theorem orderOK_of {n w : Nat} {PS : Nat → Nat} {kS oa pb e oab : Nat} (hk : 2 ≤ kS)
    (hid : bAnd(idK n w (mask w), canonK n w (mask w) (n * w) (pidn n w)) = true)
    (hc : bAnd(canonK n w (mask w) (n * w) (PS 0), canonK n w (mask w) (n * w) (PS 1)) = true)
    (h : bAnd(Nat.beq (powK n w (PS 0) oa) (pidn n w),
      bAnd(Bool.not (Nat.beq (PS 0) (pidn n w)),
      bAnd(Nat.beq (powK n w (PS 1) (pb ^ (e + 1))) (pidn n w),
      bAnd(Bool.not (Nat.beq (powK n w (PS 1) (pb ^ e)) (pidn n w)),
      bAnd(Nat.beq (powK n w (pcomp n w (mask w) (PS 0) (PS 1)) oab) (pidn n w),
      Bool.not (Nat.beq (pcomp n w (mask w) (PS 0) (PS 1)) (pidn n w))))))) = true) :
    fo22OrderOK n (SA n w kS PS) oa pb e oab = true := by
  obtain ⟨hidA, hcid⟩ := (bAnd_iff _ _).1 hid
  obtain ⟨hc0, hc1⟩ := (bAnd_iff _ _).1 hc
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hc01 := canonK_pcomp hc0 hc1
  have e0 : (SA n w kS PS)[0]! = unpack n w (PS 0) := ofFn_get (by omega)
  have e1 : (SA n w kS PS)[1]! = unpack n w (PS 1) := ofFn_get (by omega)
  unfold fo22OrderOK
  rw [e0, e1, ← idK_sound hidA, compA_unpack hc0 hc1, powA_unpack hcid hidA hc0,
    powA_unpack hcid hidA hc1, powA_unpack hcid hidA hc1, powA_unpack hcid hidA hc01,
    eqA_unpack (canonK_powK hcid hc0 _) hcid, eqA_unpack hc0 hcid,
    eqA_unpack (canonK_powK hcid hc1 _) hcid, eqA_unpack (canonK_powK hcid hc1 _) hcid,
    eqA_unpack (canonK_powK hcid hc01 _) hcid, eqA_unpack hc01 hcid, h1, h3, h5]
  simp only [Bool.not_eq_true'] at h2 h4 h6
  rw [h2, h4, h6]
  rfl

theorem order3 : fo22OrderOK 1575 fo22P3Strong 3 5 0 7 = true := by
  rw [p3S]
  exact orderOK_of (by norm_num) Fo22M.id3 Fo22M.cP3 Fo22M.ord3

theorem order4 : fo22OrderOK 63 fo22P4Strong 3 2 2 7 = true := by
  rw [p4S]
  exact orderOK_of (by norm_num) Fo22M.id4 Fo22M.cP4 Fo22M.ord4

end CertificateChecks.KernelSpor.Fo22C

end
