module

public import Certificates.Kernel.LocalComp.J2Std.Pack
public import Certificates.Kernel.LocalComp.J2Std.OrbZ
public import Certificates.Kernel.LocalComp.J2Std.OrbH
public import Certificates.Kernel.Misc.Perm.J2Mult5
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelLC.J2Std

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.J2StdOrb
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.RankTwoClassical.J2Std

@[expose] public noncomputable def twoK (i : Nat) : Bool :=
  (!(Nat.beq (sqk 7 (C1.T i)) (pidn 315 9))) || (List.range H.N).any (fun j => Nat.beq (C1.T i) (H.T j))

@[expose] public noncomputable def twoSl (s : Nat) : Bool :=
  allN 5 (fun d => twoK (Nat.add (Nat.mul 5 s) d))

@[expose] public noncomputable def HG (i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) H0P (fun _ _ => H1P) i

@[expose] public def wd (k i : Nat) : List Nat := (j2StdSW.getD k #[]).getD i []

@[expose] public noncomputable def cgK (k : Nat) : Bool :=
  Nat.beq (H.T k) (pidn 315 9) || allN 2 (fun i => (wd k i).all (fun j => decide (j < 60)) &&
    Nat.beq (foldConj H.T k (pidn 315 9) (wd k i)) (HG i))

@[expose] public noncomputable def CJ (i : Nat) : Nat := pkA 9 j2StdConj[i]!

@[expose] public noncomputable def WW (i : Nat) : Nat := pkA 9 j2StdW[i]!

@[expose] public noncomputable def zsel (j : Nat) : Nat := nIf(Nat.beq j 0, Z1P, Z2P)

@[expose] public noncomputable def p5K (i : Nat) : Bool :=
  okK (CJ i) && okK (WW i) && canonK 315 9 (mask 9) (315 * 9) (CJ i) &&
    canonK 315 9 (mask 9) (315 * 9) (WW i) && canonK 315 9 (mask 9) (315 * 9) (iv (CJ i)) &&
    Nat.beq (cj (CJ i) (WW i)) (pw (zsel j2StdJ[i]!) j2StdK[i]!) &&
    (j2StdK[i]! == 1 || j2StdK[i]! == 2)

end CertificateChecks.KernelLC.J2Std

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelLC.J2Std.OTwo CertificateChecks.KernelLC.J2Std.twoSl 60
#kss_each CertificateChecks.KernelLC.J2Std.OCG CertificateChecks.KernelLC.J2Std.cgK 60
#kss_each CertificateChecks.KernelLC.J2Std.OP5 CertificateChecks.KernelLC.J2Std.p5K 24

namespace CertificateChecks.KernelLC.J2Std

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.J2StdOrb
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.RankTwoClassical.J2Std CertificateChecks.KernelJ2Cover
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts okA inCert isTwoA)
open CFSG.Monster.B.Mathieu (powArr)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem bC1 : j2StdC1.size = C1.ng ∧ ∀ k < C1.ng, j2StdC1[k]! = unpack 315 9 (C1.G k) :=
  binds_of_listK rfl (by quickRfl)
theorem bC2 : j2StdC2.size = C2.ng ∧ ∀ k < C2.ng, j2StdC2[k]! = unpack 315 9 (C2.G k) :=
  binds_of_listK rfl (by quickRfl)
theorem bCH : j2StdCH.size = CH.ng ∧ ∀ k < CH.ng, j2StdCH[k]! = unpack 315 9 (CH.G k) :=
  binds_of_listK rfl (by quickRfl)

theorem hHG0 : H.G 0 = H0P := Nat.eq_of_beq_eq_true (by quickRfl)
theorem hHG1 : H.G 1 = H1P := Nat.eq_of_beq_eq_true (by quickRfl)

theorem bH : j2StdH.size = H.ng ∧ ∀ k < H.ng, j2StdH[k]! = unpack 315 9 (H.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk' : k < 2 := hk
  have e0 : j2StdH[0]! = j2StdH0 := rfl
  have e1 : j2StdH[1]! = j2StdH1 := rfl
  interval_cases k
  · rw [e0, hH0, hHG0]
  · rw [e1, hH1, hHG1]

abbrev SetFacts (c : CFSG.Monster.B.Fischer.ArrCert) (gs : Array (Array Nat)) (N : Nat)
    (T : Nat → Nat) : Prop :=
  enumOK 315 gs keyPts c = true ∧ (∀ x, x ∈ c.pts ↔ ∃ i < N, unpack 315 9 (T i) = x) ∧
    c.pts.size = N

theorem setC1 : SetFacts cStdC1 j2StdC1 C1.N C1.T :=
  setOf bC1.1 bC1.2 (by quickRfl) C1.ok (by quickRfl) (by decide)
theorem setC2 : SetFacts cStdC2 j2StdC2 C2.N C2.T :=
  setOf bC2.1 bC2.2 (by quickRfl) C2.ok (by quickRfl) (by decide)
theorem setH : SetFacts cStdH j2StdH H.N H.T :=
  setOf bH.1 bH.2 (by quickRfl) H.ok (by quickRfl) (by decide)
theorem setCH : SetFacts cStdCH j2StdCH CH.N CH.T :=
  setOf bCH.1 bCH.2 (by quickRfl) CH.ok (by quickRfl) (by decide)

theorem kC1 : allN C1.ng (fun k => okK (C1.G k) &&
    Nat.beq (cm (C1.G k) Z1P) (cm Z1P (C1.G k))) = true := by quickRfl
theorem kC2 : allN C2.ng (fun k => okK (C2.G k) &&
    Nat.beq (cm (C2.G k) Z2P) (cm Z2P (C2.G k))) = true := by quickRfl
theorem kCH : allN CH.ng (fun k => okK (CH.G k) && Nat.beq (cm (CH.G k) H0P) (cm H0P (CH.G k)) &&
    Nat.beq (cm (CH.G k) H1P) (cm H1P (CH.G k))) = true := by quickRfl
theorem kH : allN H.ng (fun k => okK (H.G k)) = true := by quickRfl

theorem cZ1 : Can Z1P := by quickRfl
theorem cZ2 : Can Z2P := by quickRfl
theorem cH0 : Can H0P := by quickRfl
theorem cH1 : Can H1P := by quickRfl

theorem okU {p : Nat} (h : okK p = true) : okA (unpack 315 9 p) = true := okK_sound h

theorem gcan {ng : Nat} {G : Nat → Nat}
    (h : allN ng (fun k => canonK 315 9 (mask 9) (Nat.mul 315 9) (G k)) = true) :
    ∀ k < ng, Can (G k) := fun k hk => allN_spec h k hk

theorem elts : j2StdElts = true := by
  unfold j2StdElts
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  and_intros
  · rw [hZ1]; exact okU (by quickRfl)
  · rw [hZ2]; exact okU (by quickRfl)
  · rw [hZ1, powArr_unpack cZ1 5, hid, eqU (pw_can cZ1 5) kPid]; quickRfl
  · rw [hZ1, hid, eqU cZ1 kPid]; quickRfl
  · rw [hZ2, powArr_unpack cZ2 5, hid, eqU (pw_can cZ2 5) kPid]; quickRfl
  · rw [hZ2, hid, eqU cZ2 kPid]; quickRfl
  · intro i hi
    rw [bC1.1] at hi
    have h := allN_spec kC1 i hi
    rw [Bool.and_eq_true] at h
    rw [bC1.2 i hi, hZ1, commA_unpack (gcan C1.hG i hi) cZ1]
    exact ⟨okU h.1, h.2⟩
  · intro i hi
    rw [bC2.1] at hi
    have h := allN_spec kC2 i hi
    rw [Bool.and_eq_true] at h
    rw [bC2.2 i hi, hZ2, commA_unpack (gcan C2.hG i hi) cZ2]
    exact ⟨okU h.1, h.2⟩
  · rw [hA1]; exact okU (by quickRfl)
  · rw [hB1]; exact okU (by quickRfl)
  · rw [hA2]; exact okU (by quickRfl)
  · rw [hB2]; exact okU (by quickRfl)
  · rw [hA1, hZ1, commA_unpack (by quickRfl) cZ1]; quickRfl
  · rw [hB1, hZ1, commA_unpack (by quickRfl) cZ1]; quickRfl
  · rw [hA2, hZ1, commA_unpack (by quickRfl) cZ1]; quickRfl
  · rw [hB2, hZ1, commA_unpack (by quickRfl) cZ1]; quickRfl
  · intro i hi
    rw [bCH.1] at hi
    have h := allN_spec kCH i hi
    simp only [Bool.and_eq_true] at h
    rw [bCH.2 i hi]
    exact okU h.1.1
  · intro i hi
    rw [bH.1] at hi
    rw [bH.2 i hi]
    exact okU (allN_spec kH i hi)
  · exact setC1.1
  · exact setC1.2.2
  · exact setC2.1
  · exact setC2.2.2
  · exact setH.1
  · exact setH.2.2
  · exact setCH.1
  · exact setCH.2.2

theorem two_all : ∀ i < C1.N, twoK i = true := by
  intro i hi
  have hs : i / 5 < 60 := by
    have : C1.N = 300 := rfl
    omega
  have h := allN_spec (OTwo.all (i / 5) hs) (i % 5) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 5 (i / 5)) (i % 5) = i := Nat.div_add_mod i 5
  rwa [e] at h

theorem permH : allN H.N (fun i => permOK 315 9 (mask 9) (315 * 9) (H.T i) (iv (H.T i)) &&
    canonK 315 9 (mask 9) (315 * 9) (iv (H.T i))) = true := by quickRfl

theorem hchk : j2StdHChk = true := by
  unfold j2StdHChk
  rw [Bool.and_eq_true]
  have hcH := bfsK_canon H.ok
  constructor
  · refine allLt_pts (f := fun x => !(isTwoA x) || inCert cStdH x) setC1.2.1 fun i hi => ?_
    have hc := bfsK_canon C1.ok i hi
    rw [isTwoA_unpack hc, inCert_unpack setH.2.1 hc hcH]
    exact two_all i hi
  · have hpos : cStdH.pts = Array.ofFn (n := H.N) fun i => unpack 315 9 (H.T i.val) :=
      ptsOf bH.1 bH.2 H.ok (by quickRfl) (by decide)
    have hsz : cStdH.pts.size = 60 := by rw [hpos, Array.size_ofFn]; rfl
    have hpm : ∀ i < H.N, PermP (H.T i) := fun i hi => by
      have h := allN_spec permH i hi
      rw [Bool.and_eq_true] at h
      exact h.1
    have hci : ∀ i < H.N, Can (iv (H.T i)) := fun i hi => by
      have h := allN_spec permH i hi
      rw [Bool.and_eq_true] at h
      exact h.2
    unfold conjGenOK
    rw [allLt_iff]
    intro k hk
    rw [hsz] at hk
    have hk' : k < H.N := hk
    have hpk : cStdH.pts[k]! = unpack 315 9 (H.T k) := by
      rw [hpos, getElem!_pos _ k (by simpa using hk'), Array.getElem_ofFn]
    have h := OCG.all k hk
    unfold cgK at h
    rw [Bool.or_eq_true] at h
    rw [Bool.or_eq_true]
    rcases h with h | h
    · left
      rw [hpk, hid, eqU (hcH k hk') kPid]
      exact h
    · right
      rw [allLt_iff]
      intro i hi
      have hi' : i < 2 := hi
      have hw := allN_spec h i hi'
      rw [Bool.and_eq_true] at hw
      obtain ⟨hw1, hw2⟩ := hw
      have hwl : ∀ j ∈ wd k i, j < H.N := fun j hj => by
        have := List.all_eq_true.1 hw1 j hj
        have h60 : j < 60 := by simpa using this
        exact h60
      rw [Bool.and_eq_true, hsz]
      refine ⟨hw1, ?_⟩
      unfold conjProdW
      rw [hid]
      change eqA 315 ((wd k i).foldl (fun r j => compA 315 r (conjA 315 cStdH.pts[j]! cStdH.pts[k]!))
        (unpack 315 9 (pidn 315 9))) j2StdH[i]! = true
      rw [foldConj_unpack hpos hcH hpm hci hk' (wd k i) _ hwl kPid, bH.2 i hi']
      have hg : H.G i = HG i := by
        interval_cases i
        · exact hHG0
        · exact hHG1
      rw [eqU (foldConj_can hcH hci hk' (wd k i) (pidn 315 9) hwl kPid) (gcan H.hG i hi'), hg]
      exact hw2

theorem cHP : allN 25 (fun k => canonK 315 9 (mask 9) (315 * 9) (CertificateChecks.KernelMisc.J2M5.HP.F k)) =
    true := by quickRfl

theorem kE25 : allN 25 (fun k => Nat.beq (CertificateChecks.KernelMisc.J2M5.HP.F k) (pidn 315 9) ||
    (List.range 24).any (fun i => Nat.beq (CertificateChecks.KernelMisc.J2M5.HP.F k) (WW i))) =
      true := by quickRfl

theorem bW : allN 24 (fun i => bindListK 315 9 (WW i) j2StdW[i]!.toList) = true := by quickRfl
theorem bCJ : allN 24 (fun i => bindListK 315 9 (CJ i) j2StdConj[i]!.toList) = true := by quickRfl
theorem cWW : allN 24 (fun i => canonK 315 9 (mask 9) (315 * 9) (WW i)) = true := by quickRfl

theorem powZ (j k : Nat) : powArr 315 (j2StdZ j) k = unpack 315 9 (pw (zsel j) k) := by
  cases j with
  | zero =>
    simp only [j2StdZ, ↓reduceIte]
    rw [hZ1, powArr_unpack cZ1]
    rfl
  | succ j =>
    simp only [j2StdZ, Nat.add_one_ne_zero, ↓reduceIte]
    rw [hZ2, powArr_unpack cZ2]
    rfl

theorem p5 : j2StdP5 = true := by
  have hW : ∀ i < 24, j2StdW[i]! = unpack 315 9 (WW i) := fun i hi =>
    eq_unpack_of_bindListK (allN_spec bW i hi)
  have hC : ∀ i < 24, j2StdConj[i]! = unpack 315 9 (CJ i) := fun i hi =>
    eq_unpack_of_bindListK (allN_spec bCJ i hi)
  have hWs : j2StdW.size = 24 := Nat.eq_of_beq_eq_true (by quickRfl)
  unfold j2StdP5
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨by quickRfl, by quickRfl⟩, by quickRfl⟩, by quickRfl⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro i hi
    have h := OP5.all i hi
    unfold p5K at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    have hpC : PermP (CJ i) := ((bAnd_iff _ _).1 h1).1
    have hz : Can (zsel j2StdJ[i]!) := by
      unfold zsel
      cases Nat.beq j2StdJ[i]! 0
      exacts [cZ2, cZ1]
    rw [hC i hi, hW i hi, conjA_unpack hpC h3 h4 h5, powZ, eqU (cj_can h3 h4 h5) (pw_can hz _)]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨okU h1, okU h2⟩, h6⟩, h7⟩
  · rw [allLt_iff]
    intro k hk
    have hk' : k < 25 := by simpa [CFSG.RankThree.PartTwo.KFacts.KS14.cE25,
      CFSG.RankThree.PartTwo.KFacts.KS14.cE25Lit] using hk
    have h := allN_spec kE25 k hk'
    have hc := allN_spec cHP k hk'
    rw [CertificateChecks.KernelMisc.J2M5.pts_get k hk', Bool.or_eq_true]
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · left
      rw [hid, eqU hc kPid]
      exact h
    · right
      obtain ⟨j, hj, e⟩ := List.any_eq_true.1 h
      rw [List.mem_range] at hj
      rw [Array.any_eq_true]
      refine ⟨j, by rw [hWs]; exact hj, ?_⟩
      rw [← getElem!_pos j2StdW j (by rw [hWs]; exact hj), hW j hj, eqU hc (allN_spec cWW j hj)]
      exact e

theorem orb : j2StdOrb = true := by
  unfold j2StdOrb
  rw [orbZ1, orbZ2, orbH, Bool.true_and, Bool.true_and, Bool.true_and, allLt_iff]
  intro i hi
  rw [bCH.1] at hi
  have h := allN_spec kCH i hi
  simp only [Bool.and_eq_true] at h
  rw [bCH.2 i hi, hH0, hH1, commA_unpack (gcan CH.hG i hi) cH0,
    commA_unpack (gcan CH.hG i hi) cH1, Bool.and_eq_true]
  exact ⟨h.1.2, h.2⟩

theorem j2StdCheck_eq_true : j2StdCheck = true := by
  unfold j2StdCheck
  rw [elts, hchk, p5, orb]
  rfl

end CertificateChecks.KernelLC.J2Std

end
