module

public import Certificates.Kernel.LocalComp.J2Std.OrbBase
public import Certificates.Kernel.LocalComp.J2Std.Enum
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44J2Tests
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.J2Std

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.J2StdOrb
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.RankTwoClassical.J2Std CertificateChecks.KernelJ2Cover
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts okA inCert isTwoA)
open CFSG.Monster.B.Mathieu (powArr)

@[expose] noncomputable def okK (p : Nat) : Bool :=
  bAnd(permOK 315 9 (mask 9) (315 * 9) p (iv p), bAnd(Nat.beq (Nat.shiftRight p (315 * 9)) 0,
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 p))

theorem okK_sound {p : Nat} (h : okK p = true) : okA (unpack 315 9 p) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  unfold okA
  rw [Bool.and_eq_true]
  exact ⟨validA_unpack h1, inP_of rfl h2 (range_of_permOK h1) h3⟩

theorem kId : idK 315 9 (mask 9) = true := by quickRfl
theorem kPid : Can (pidn 315 9) := by quickRfl
theorem hid : idA 315 = unpack 315 9 (pidn 315 9) := (idK_sound kId).symm

theorem eqU {p q : Nat} (hp : Can p) (hq : Can q) :
    eqA 315 (unpack 315 9 p) (unpack 315 9 q) = Nat.beq p q := eqA_unpack hp hq

theorem commA_unpack {p q : Nat} (hp : Can p) (hq : Can q) :
    CFSG.ComponentClassification.J2Cover.commA (unpack 315 9 p) (unpack 315 9 q) =
      Nat.beq (cm p q) (cm q p) := by
  unfold CFSG.ComponentClassification.J2Cover.commA
  rw [cm_eq hp hq, cm_eq hq hp, eqU (p := cm p q) (q := cm q p) (canonK_pcomp hp hq)
    (canonK_pcomp hq hp)]

theorem can_cm {p q : Nat} (hp : Can p) (hq : Can q) : Can (cm p q) := canonK_pcomp hp hq

@[expose] noncomputable def pw (p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 315 9) (fun _ acc => cm p acc) k

theorem pw_can {p : Nat} (hp : Can p) : ∀ k, Can (pw p k)
  | 0 => kPid
  | k + 1 => can_cm hp (pw_can hp k)

theorem powArr_unpack {p : Nat} (hp : Can p) : ∀ k,
    powArr 315 (unpack 315 9 p) k = unpack 315 9 (pw p k)
  | 0 => hid
  | k + 1 => by
    rw [powArr, powArr_unpack hp k, cm_eq hp (pw_can hp k)]
    rfl

@[expose] noncomputable def sqk (k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun p => p) (fun _ ih p => ih (cm p p)) k

theorem sqk_can : ∀ k {p : Nat}, Can p → Can (sqk k p)
  | 0, _, hp => hp
  | k + 1, _, hp => sqk_can k (can_cm hp hp)

theorem sqIterA_unpack : ∀ k {p : Nat}, Can p →
    CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.sqIterA k (unpack 315 9 p) = unpack 315 9 (sqk k p)
  | 0, _, _ => rfl
  | k + 1, p, hp => by
    rw [CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.sqIterA, CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.sqA,
      cm_eq hp hp, sqIterA_unpack k (can_cm hp hp)]
    rfl

theorem isTwoA_unpack {p : Nat} (hp : Can p) :
    isTwoA (unpack 315 9 p) = Nat.beq (sqk 7 p) (pidn 315 9) := by
  unfold isTwoA
  rw [sqIterA_unpack 7 hp, hid, eqU (sqk_can 7 hp) kPid]

@[expose] noncomputable def cj (g y : Nat) : Nat := cm g (cm y (iv g))

theorem conjA_unpack {g y : Nat} (hg : PermP g) (cg : Can g) (cy : Can y) (cgi : Can (iv g)) :
    conjA 315 (unpack 315 9 g) (unpack 315 9 y) = unpack 315 9 (cj g y) := by
  unfold conjA
  rw [iv_eq hg, cm_eq cy cgi, cm_eq (q := cm y (iv g)) cg (can_cm cy cgi)]
  rfl

theorem cj_can {g y : Nat} (cg : Can g) (cy : Can y) (cgi : Can (iv g)) : Can (cj g y) :=
  can_cm cg (can_cm cy cgi)

theorem commutatorA_unpack {p q : Nat} (hp : PermP p) (hq : PermP q) (cp : Can p) (cq : Can q)
    (cpi : Can (iv p)) (cqi : Can (iv q)) :
    commutatorA 315 (unpack 315 9 p) (unpack 315 9 q) = unpack 315 9 (cmt p q) :=
  cmt_eq hp hq cp cq cpi cqi

theorem cmt_can {p q : Nat} (cp : Can p) (cq : Can q) (cpi : Can (iv p)) (cqi : Can (iv q)) :
    Can (cmt p q) := can_cm (can_cm cp cq) (can_cm cpi cqi)

theorem keyPts_lt : ∀ p ∈ keyPts, p < 315 := by decide

theorem setOf {gs : Array (Array Nat)} {ng N fuel : Nat} {G T E S : Nat → Nat}
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack 315 9 (G k))
    (hp : allN ng (fun k => permOK 315 9 (mask 9) (315 * 9) (G k) (pinvS 315 9 (mask 9) (G k))) =
      true)
    (hk : bfsK 315 9 ng G N T E S = true) (hkey : keysK 315 9 keyPts N T = true) (hf : N ≤ fuel) :
    enumOK 315 gs keyPts (enumBfs 315 gs keyPts fuel) = true ∧
      (∀ x, x ∈ (enumBfs 315 gs keyPts fuel).pts ↔ ∃ i < N, unpack 315 9 (T i) = x) ∧
      (enumBfs 315 gs keyPts fuel).pts.size = N :=
  enumBfs_of_bfsK_set hs hg (fun k hk => allN_spec hp k hk) kId kPid hk keyPts_lt hkey hf

theorem ptsOf {gs : Array (Array Nat)} {ng N fuel : Nat} {G T E S : Nat → Nat}
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack 315 9 (G k))
    (hk : bfsK 315 9 ng G N T E S = true) (hkey : keysK 315 9 keyPts N T = true) (hf : N ≤ fuel) :
    (enumBfs 315 gs keyPts fuel).pts = Array.ofFn (n := N) fun i => unpack 315 9 (T i.val) :=
  enumBfs_pts_of_inj hs hg hk (fun a ha b hb e => keysK_spec hkey a ha b hb (by
    rwa [keyA_unpack keyPts_lt, keyA_unpack keyPts_lt] at e)) hf

theorem inCert_unpack {c : CFSG.Monster.B.Fischer.ArrCert} {N P : Nat} {T : Nat → Nat}
    (hmem : ∀ x, x ∈ c.pts ↔ ∃ i < N, unpack 315 9 (T i) = x) (hP : Can P)
    (hT : ∀ i < N, Can (T i)) :
    inCert c (unpack 315 9 P) = (List.range N).any (fun i => Nat.beq P (T i)) := by
  unfold inCert
  rw [any_pts hmem, any_eqA_unpack_range hP hT]

@[expose] noncomputable def foldConj (T : Nat → Nat) (k r : Nat) (w : List Nat) : Nat :=
  w.foldl (fun r j => cm r (cj (T j) (T k))) r

theorem foldConj_can {N : Nat} {T : Nat → Nat} (hc : ∀ i < N, Can (T i))
    (hci : ∀ i < N, Can (iv (T i))) {k : Nat} (hk : k < N) :
    ∀ (w : List Nat) (r : Nat), (∀ j ∈ w, j < N) → Can r → Can (foldConj T k r w)
  | [], _, _, hr => hr
  | j :: w, r, hw, hr => by
    have hj := hw j List.mem_cons_self
    unfold foldConj
    rw [List.foldl_cons]
    exact foldConj_can hc hci hk w _ (fun j' hj' => hw j' (List.mem_cons_of_mem _ hj'))
      (can_cm hr (cj_can (hc j hj) (hc k hk) (hci j hj)))

theorem foldConj_unpack {N : Nat} {T : Nat → Nat} {pts : Array (Array Nat)}
    (hpts : pts = Array.ofFn (n := N) fun i => unpack 315 9 (T i.val))
    (hc : ∀ i < N, Can (T i)) (hpm : ∀ i < N, PermP (T i)) (hci : ∀ i < N, Can (iv (T i)))
    {k : Nat} (hk : k < N) :
    ∀ (w : List Nat) (r : Nat), (∀ j ∈ w, j < N) → Can r →
      w.foldl (fun r j => compA 315 r (conjA 315 pts[j]! pts[k]!)) (unpack 315 9 r) =
        unpack 315 9 (foldConj T k r w)
  | [], _, _, _ => rfl
  | j :: w, r, hw, hr => by
    have hj := hw j List.mem_cons_self
    have hpt : ∀ i < N, pts[i]! = unpack 315 9 (T i) := fun i hi => by
      rw [hpts, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
    have e : compA 315 (unpack 315 9 r) (conjA 315 pts[j]! pts[k]!) =
        unpack 315 9 (cm r (cj (T j) (T k))) := by
      rw [hpt j hj, hpt k hk, conjA_unpack (hpm j hj) (hc j hj) (hc k hk) (hci j hj),
        cm_eq hr (cj_can (hc j hj) (hc k hk) (hci j hj))]
    rw [List.foldl_cons]
    change List.foldl _ (compA 315 (unpack 315 9 r) (conjA 315 pts[j]! pts[k]!)) w = _
    rw [e]
    exact foldConj_unpack hpts hc hpm hci hk w _ (fun j' hj' => hw j' (List.mem_cons_of_mem _ hj'))
      (can_cm hr (cj_can (hc j hj) (hc k hk) (hci j hj)))

end CertificateChecks.KernelLC.J2Std

end
