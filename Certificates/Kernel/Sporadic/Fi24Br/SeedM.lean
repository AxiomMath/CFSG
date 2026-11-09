module

public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import CFSG.Certificates.Kernel.LocalCompOps3Snd.Bridge
public import Certificates.Data.Kernel.LocalQT.SecF3
public import CFSG.Certificates.Kernel.Spor.Mat3Sound
import Certificates.Kernel.Sporadic.Fi24Br.Rels
import CFSG.Certificates.Kernel.LocalQT.StepsF3Sound
import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CertificateChecks.KernelSpor.Fi24Rels

open CFSG.KC.LQT CFSG.KC.Ord CFSG.KD.BrFi24 CFSG.KC.LocalComp.Ops3Snd

theorem seedM_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = 781) {X M : Nat}
    {s : String} {l : List Char} (hs : CFSG.Blueprint.NativeSporadic.decode 3 781 1 s =
      CFSG.KS.Mat3.mat3 781 609961 M) (hl : s = String.ofList l)
    (hv : validM c.p (c.d * c.S) c.L c.H X = true)
    (hg : Nat.beq (Nat.lor (gath3 c.w 20 X).p (Nat.shiftLeft (gath3 c.w 20 X).m 609961)) M =
      true) :
    SeedM c X l := by
  have hX := CFSG.KS.Ord.validM_canon hc hv
  obtain ⟨-, hS, hw0, hpw⟩ := CFSG.KS.SporSch.LyM.cfacts hc
  obtain ⟨p, w, S, d, T, L, H, CM, RM, ONE, LV, HV⟩ := c
  dsimp only at hp hd hX hS hw0 hpw hg ⊢
  subst hp hd hS
  have hw : 2 ≤ w := by
    rcases Nat.lt_or_ge w 2 with h | h
    · interval_cases w
      norm_num at hpw
    · exact h
  refine ⟨hX, ?_⟩
  unfold mat3
  dsimp only
  rw [← hl, hs, CFSG.KC.LQT.F3S.mat3_of_gath hw (K := 20) (by norm_num) (by norm_num) hX hg]

theorem seedM_A {c : Lay} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = 781) {X : Nat}
    {l : List Char} (hl : CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 = String.ofList l)
    (hv : validM c.p (c.d * c.S) c.L c.H X = true)
    (hg : Nat.beq (Nat.lor (gath3 c.w 20 X).p (Nat.shiftLeft (gath3 c.w 20 X).m 609961)) (RB 23) =
      true) :
    SeedM c X l :=
  seedM_of hc hp hd mA_eq hl hv hg

theorem seedM_B {c : Lay} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = 781) {X : Nat}
    {l : List Char} (hl : CFSG.Blueprint.NativeSporadic.Fi24primeSeed2 = String.ofList l)
    (hv : validM c.p (c.d * c.S) c.L c.H X = true)
    (hg : Nat.beq (Nat.lor (gath3 c.w 20 X).p (Nat.shiftLeft (gath3 c.w 20 X).m 609961)) (RB 24) =
      true) :
    SeedM c X l :=
  seedM_of hc hp hd mB_eq hl hv hg

end CertificateChecks.KernelSpor.Fi24Rels

end
