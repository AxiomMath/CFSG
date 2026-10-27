
module

public import Certificates.Kernel.Sporadic.ON4.Defs
public import Certificates.Kernel.Sporadic.ON4.Words

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON4K

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KS.TW CFSG.KS.PW CertificateChecks.KernelSpor.ON3
open CFSG.Sporadic.ON.Native (nPts)

@[expose] def Pair1 (f fi : Nat → Nat) : Prop :=
  ∀ y < 245520, f y < 245520 ∧ fi y < 245520 ∧ fi (f y) = y ∧ f (fi y) = y

theorem comp_pair {f fi g gi : Nat → Nat} (hf : Pair1 f fi) (hg : Pair1 g gi) :
    Pair1 (fun y => f (g y)) (fun y => gi (fi y)) := by
  intro y hy
  obtain ⟨g1, g2, g3, g4⟩ := hg y hy
  obtain ⟨f1, f2, f3, f4⟩ := hf y hy
  refine ⟨(hf _ g1).1, (hg _ f2).2.1, ?_, ?_⟩
  · simp only []
    rw [(hf _ g1).2.2.1, g3]
  · simp only []
    rw [(hg _ f2).2.2.2, f4]

theorem inv_pair {f fi : Nat → Nat} (hf : Pair1 f fi) : Pair1 fi f := fun y hy =>
  ⟨(hf y hy).2.1, (hf y hy).1, (hf y hy).2.2.2, (hf y hy).2.2.1⟩

theorem pair_of {s : Nat} {G GI : Nat → Nat → Nat} (h : InvPair 245520 s G GI) {j : Nat}
    (hj : j < s) : Pair1 (G j) (GI j) := h j hj

theorem pair_inv {s : Nat} {G GI : Nat → Nat → Nat} (h : ∀ j < s, Pair1 (G j) (GI j)) :
    InvPair 245520 s G GI := h

theorem mcO_pair : InvPair 245520 3 mcO mcOI := by
  have A := pair_of mG_pair (j := 1) (by norm_num)
  have B := pair_of mG_pair (j := 2) (by norm_num)
  have P1 := comp_pair (f := mGI 2) (fi := mG 2) (g := mGI 1) (gi := mG 1) (inv_pair B)
    (inv_pair A)
  have P2 := comp_pair (f := mG 1) (fi := mGI 1) A P1
  have X := comp_pair (f := mG 2) (fi := mGI 2) B P2
  intro j hj y hy
  interval_cases j
  · exact X y hy
  · exact comp_pair A (comp_pair X (inv_pair A)) y hy
  · exact comp_pair B (comp_pair X (inv_pair B)) y hy

theorem lcO_pair : InvPair 245520 3 lcO lcOI := by
  have A := pair_of lG_pair (j := 0) (by norm_num)
  have B := pair_of lG_pair (j := 1) (by norm_num)
  have P1 := comp_pair (f := lGI 1) (fi := lG 1) (g := lGI 0) (gi := lG 0) (inv_pair B)
    (inv_pair A)
  have P2 := comp_pair (f := lG 0) (fi := lGI 0) A P1
  have X := comp_pair (f := lG 1) (fi := lGI 1) B P2
  intro j hj y hy
  interval_cases j
  · exact X y hy
  · exact comp_pair A (comp_pair X (inv_pair A)) y hy
  · exact comp_pair B (comp_pair X (inv_pair B)) y hy

theorem c_pair : Pair1 CT CIT := fun y hy =>
  ⟨(c_get y hy).2, (c_CI hy).2, (tab_facts hy).2.2.2.1, (c_CI hy).1⟩

theorem jO_pair : InvPair 245520 6 jO jOI := by
  intro j hj y hy
  interval_cases j
  · exact mG_pair 0 (by norm_num) y hy
  · exact mG_pair 1 (by norm_num) y hy
  · exact mG_pair 2 (by norm_num) y hy
  · exact comp_pair c_pair (comp_pair (pair_of mG_pair (j := 0) (by norm_num)) (inv_pair c_pair)) y hy
  · exact comp_pair c_pair (comp_pair (pair_of mG_pair (j := 1) (by norm_num)) (inv_pair c_pair)) y hy
  · exact comp_pair c_pair (comp_pair (pair_of mG_pair (j := 2) (by norm_num)) (inv_pair c_pair)) y hy

theorem nIf_t {c : Bool} (hc : c = true) {t e : Nat} : nIf(c, t, e) = t := by
  subst hc
  rfl

theorem pair_ext {k : Nat} {G GI : Nat → Nat → Nat} {G' GI' : Nat → Nat → Nat} {S SI : Nat → Nat}
    (hp : InvPair 245520 k G GI) (hlo : ∀ i < k, G' i = G i ∧ GI' i = GI i)
    (hk : G' k = S ∧ GI' k = SI) {w : List Int} (hw : LetM k w)
    (hS : ∀ x, S x = w.foldr (GZ G GI) x) (hSI : ∀ x, SI x = (invW w).foldr (GZ G GI) x) :
    InvPair 245520 (k + 1) G' GI' := by
  intro i hi y hy
  rcases Nat.lt_or_ge i k with h | h
  · rw [(hlo i h).1, (hlo i h).2]
    exact hp i h y hy
  · have e : i = k := by omega
    subst e
    rw [hk.1, hk.2, hS, hS, hSI, hSI]
    exact invPair_word hp hw y hy

theorem mcF_pair : InvPair 245520 5 mcF mcFI := by
  have p4 : InvPair 245520 4 mcO4 mcOI4 := pair_ext mcO_pair
    (fun i hi => ⟨by funext x; unfold mcO4; rw [nIf_t (blt_of hi)],
      by funext x; unfold mcOI4; rw [nIf_t (blt_of hi)]⟩) ⟨rfl, rfl⟩ lets4.1
    (fun x => tr4_word _ _ (k := 0) (by norm_num) x) (fun x => tr4_inv _ _ (k := 0) (by norm_num) x)
  exact pair_ext p4
    (fun i hi => ⟨by funext x; unfold mcF; rw [nIf_t (blt_of hi)],
      by funext x; unfold mcFI; rw [nIf_t (blt_of hi)]⟩) ⟨rfl, rfl⟩ lets4.2.1
    (fun x => tr4_word _ _ (k := 1) (by norm_num) x) (fun x => tr4_inv _ _ (k := 1) (by norm_num) x)

theorem lcF_pair : InvPair 245520 6 lcF lcFI := by
  have p4 : InvPair 245520 4 lcO4 lcOI4 := pair_ext lcO_pair
    (fun i hi => ⟨by funext x; unfold lcO4; rw [nIf_t (blt_of hi)],
      by funext x; unfold lcOI4; rw [nIf_t (blt_of hi)]⟩) ⟨rfl, rfl⟩ lets4.2.2.1
    (fun x => tr4_word _ _ (k := 2) (by norm_num) x) (fun x => tr4_inv _ _ (k := 2) (by norm_num) x)
  have p5 : InvPair 245520 5 lcO5 lcOI5 := pair_ext p4
    (fun i hi => ⟨by funext x; unfold lcO5; rw [nIf_t (blt_of hi)],
      by funext x; unfold lcOI5; rw [nIf_t (blt_of hi)]⟩) ⟨rfl, rfl⟩ lets4.2.2.2.1
    (fun x => tr4_word _ _ (k := 3) (by norm_num) x) (fun x => tr4_inv _ _ (k := 3) (by norm_num) x)
  exact pair_ext p5
    (fun i hi => ⟨by funext x; unfold lcF; rw [nIf_t (blt_of hi)],
      by funext x; unfold lcFI; rw [nIf_t (blt_of hi)]⟩) ⟨rfl, rfl⟩ lets4.2.2.2.2.1
    (fun x => tr4_word _ _ (k := 4) (by norm_num) x) (fun x => tr4_inv _ _ (k := 4) (by norm_num) x)

theorem jF_pair : InvPair 245520 9 jF jFI := by
  have p7 : InvPair 245520 7 jO7 jOI7 := pair_ext jO_pair
    (fun i hi => ⟨by funext x; unfold jO7; rw [nIf_t (blt_of hi)],
      by funext x; unfold jOI7; rw [nIf_t (blt_of hi)]⟩) ⟨rfl, rfl⟩ lets4.2.2.2.2.2.1
    (fun x => tr4_word _ _ (k := 5) (by norm_num) x) (fun x => tr4_inv _ _ (k := 5) (by norm_num) x)
  have p8 : InvPair 245520 8 jO8 jOI8 := pair_ext p7
    (fun i hi => ⟨by funext x; unfold jO8; rw [nIf_t (blt_of hi)],
      by funext x; unfold jOI8; rw [nIf_t (blt_of hi)]⟩) ⟨rfl, rfl⟩ lets4.2.2.2.2.2.2.1
    (fun x => tr4_word _ _ (k := 6) (by norm_num) x) (fun x => tr4_inv _ _ (k := 6) (by norm_num) x)
  exact pair_ext p8
    (fun i hi => ⟨by funext x; unfold jF; rw [nIf_t (blt_of hi)],
      by funext x; unfold jFI; rw [nIf_t (blt_of hi)]⟩) ⟨rfl, rfl⟩ lets4.2.2.2.2.2.2.2
    (fun x => tr4_word _ _ (k := 7) (by norm_num) x) (fun x => tr4_inv _ _ (k := 7) (by norm_num) x)

end CertificateChecks.KernelSpor.ON4K

end
