module

public import Certificates.Kernel.Misc.Perm.J5Q
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native

@[expose] noncomputable def cj (p q : ℕ) : ℕ := cm p (cm q (pinvS 315 9 (mask 9) p))

theorem comm_eq {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true) :
    commA 315 (unpack 315 9 p) (unpack 315 9 q) = Nat.beq (cm p q) (cm q p) := by
  rw [commA, comp_unpack' hw hp hq, comp_unpack' hw hq hp,
    eqA_unpack' hw (permB_pcomp hw hp hq) (permB_pcomp hw hq hp)]
  rfl

theorem conj_eq {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true) :
    conjA 315 (unpack 315 9 p) (unpack 315 9 q) = unpack 315 9 (cj p q) :=
  conj_unpack' hw hp hq

theorem pCj {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true) :
    permB 315 9 (cj p q) = true :=
  permB_pcomp hw hp (permB_pcomp hw hq (permB_pinvS hw hp))

theorem pInv {p : ℕ} (hp : permB 315 9 p = true) : permB 315 9 (pinvS 315 9 (mask 9) p) = true :=
  permB_pinvS hw hp

@[expose] noncomputable def selC (F : ℕ → ℕ) (k : ℕ) (sel : List ℕ) (h : ℕ) : ℕ :=
  cj (F (sel.getD h 0)) (F k)

@[expose] noncomputable def selCI (F : ℕ → ℕ) (k : ℕ) (sel : List ℕ) (h : ℕ) : ℕ :=
  cj (F (sel.getD h 0)) (pinvS 315 9 (mask 9) (F k))

theorem conjSel_get {c : CFSG.Monster.B.Fischer.ArrCert} {N : ℕ} {F : ℕ → ℕ}
    (hN : c.pts.size = N) (hP : ∀ i < N, c.pts[i]! = unpack 315 9 (F i))
    (hPp : ∀ i < N, permB 315 9 (F i) = true) {k : ℕ} (hk : k < N) {sel : List ℕ}
    (hsel : ∀ j ∈ sel, j < N) :
    ∀ h < sel.length, (conjSel 315 c k sel)[h]! = unpack 315 9 (selC F k sel h) ∧
      (conjSelInv 315 c k sel)[h]! = unpack 315 9 (selCI F k sel h) ∧
      permB 315 9 (selC F k sel h) = true ∧ permB 315 9 (selCI F k sel h) = true := by
  intro h hh
  have hg : sel.getD h 0 = sel[h] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh]
  have hj : sel.getD h 0 < N := by rw [hg]; exact hsel _ (List.getElem_mem hh)
  refine ⟨?_, ?_, pCj (hPp _ hj) (hPp k hk), pCj (hPp _ hj) (pInv (hPp k hk))⟩
  · rw [getElem!_pos _ h (by simpa [conjSel] using hh)]
    simp only [conjSel, List.getElem_toArray, List.getElem_map]
    rw [← hg, hP _ hj, hP k hk, conj_eq (hPp _ hj) (hPp k hk)]
    rfl
  · rw [getElem!_pos _ h (by simpa [conjSelInv] using hh)]
    simp only [conjSelInv, List.getElem_toArray, List.getElem_map]
    rw [← hg, hP _ hj, hP k hk, inv_unpack hw (hPp k hk),
      conj_eq (hPp _ hj) (pInv (hPp k hk))]
    rfl

end CertificateChecks.KernelMisc.J2F

end
